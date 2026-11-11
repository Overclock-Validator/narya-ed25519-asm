#!/usr/bin/env python3
"""Fail-closed whole-leaf checker for Narya's x8 Niels transpose selectors.

The checker consumes the exact relocation-free ET_REL symbols and independently
reconstructs their semantic instruction transcript.  It validates the SysV GPR
prelude, every source address, masked/unmasked YMM load, shuffle, output store,
and the VZEROUPPER/RET epilogue.  The affine permission model deliberately
requires only the three active qwords of each EVEX masked load; the fourth qword
may be unreadable.

This is executable evidence and a generator input, not a replacement for the
Lean instruction semantics or a claim about physical CPU behavior.
"""
from __future__ import annotations

import argparse
import dataclasses
import hashlib
import json
import struct
from pathlib import Path
from typing import Iterable, Sequence

ET_REL = 1
EM_X86_64 = 62
SHT_RELA = 4
SHT_REL = 9
SHT_SYMTAB = 2
SHF_EXECINSTR = 0x4
STT_FUNC = 2

PROJECTIVE_SYMBOL = "narya_projective_niels_transpose_x8_asm"
AFFINE_SYMBOL = "narya_affine_niels_transpose_x8_asm"

GPRS = (
    "rax", "rcx", "rdx", "rbx", "rsp", "rbp", "rsi", "rdi",
    "r8", "r9", "r10", "r11", "r12", "r13", "r14", "r15",
)


class CheckError(RuntimeError):
    pass


@dataclasses.dataclass(frozen=True)
class Section:
    name: str
    kind: int
    flags: int
    offset: int
    size: int
    link: int
    info: int
    entsize: int


@dataclasses.dataclass(frozen=True)
class Symbol:
    name: str
    info: int
    section_index: int
    value: int
    size: int


class Elf:
    def __init__(self, data: bytes) -> None:
        self.data = data
        if len(data) < 64 or data[:4] != b"\x7fELF":
            raise CheckError("not an ELF file")
        if data[4] != 2 or data[5] != 1:
            raise CheckError("expected ELF64 little-endian")
        (etype, machine) = struct.unpack_from("<HH", data, 16)
        if etype != ET_REL or machine != EM_X86_64:
            raise CheckError(f"expected x86-64 ET_REL, got type={etype} machine={machine}")
        shoff = struct.unpack_from("<Q", data, 40)[0]
        shentsize, shnum, shstrndx = struct.unpack_from("<HHH", data, 58)
        if shentsize != 64 or shoff + shentsize * shnum > len(data):
            raise CheckError("invalid section table")
        raw = [struct.unpack_from("<IIQQQQIIQQ", data, shoff + i * 64) for i in range(shnum)]
        if not 0 <= shstrndx < shnum:
            raise CheckError("invalid shstrndx")
        shstr = raw[shstrndx]
        names = data[shstr[4] : shstr[4] + shstr[5]]

        def cstring(blob: bytes, offset: int) -> str:
            if not 0 <= offset < len(blob):
                return ""
            end = blob.find(b"\0", offset)
            if end < 0:
                end = len(blob)
            return blob[offset:end].decode("ascii")

        self.sections = [
            Section(cstring(names, row[0]), row[1], row[2], row[4], row[5], row[6], row[7], row[9])
            for row in raw
        ]
        self._raw_sections = raw

    def symbols(self) -> list[Symbol]:
        result: list[Symbol] = []
        for index, section in enumerate(self.sections):
            if section.kind != SHT_SYMTAB:
                continue
            if not 0 <= section.link < len(self.sections):
                raise CheckError("invalid symbol string table")
            strings = self.sections[section.link]
            strdata = self.data[strings.offset : strings.offset + strings.size]
            entsize = section.entsize or 24
            if entsize != 24 or section.size % entsize:
                raise CheckError("invalid ELF64 symbol table")
            for off in range(section.offset, section.offset + section.size, entsize):
                name_off, info, _other, shndx, value, size = struct.unpack_from("<IBBHQQ", self.data, off)
                end = strdata.find(b"\0", name_off)
                if end < 0:
                    end = len(strdata)
                name = strdata[name_off:end].decode("ascii") if name_off < len(strdata) else ""
                result.append(Symbol(name, info, shndx, value, size))
        return result

    def symbol_file_range(self, name: str) -> tuple[Symbol, int, int]:
        matches = [symbol for symbol in self.symbols() if symbol.name == name]
        if len(matches) != 1:
            raise CheckError(f"expected exactly one {name!r} symbol, found {len(matches)}")
        symbol = matches[0]
        if (symbol.info & 0xF) != STT_FUNC or symbol.size == 0:
            raise CheckError(f"{name} is not a nonempty function")
        if not 0 <= symbol.section_index < len(self.sections):
            raise CheckError(f"{name} has invalid section")
        section = self.sections[symbol.section_index]
        if not (section.flags & SHF_EXECINSTR):
            raise CheckError(f"{name} is not executable")
        start = section.offset + symbol.value
        end = start + symbol.size
        if end > section.offset + section.size or end > len(self.data):
            raise CheckError(f"{name} extends outside its section")
        relocations = [
            candidate.name
            for candidate in self.sections
            if candidate.kind in (SHT_RELA, SHT_REL)
            and candidate.info == symbol.section_index
            and candidate.size != 0
        ]
        if relocations:
            raise CheckError(f"{name} executable section has relocations: {', '.join(relocations)}")
        return symbol, start, end

    def symbol_bytes(self, name: str) -> tuple[Symbol, bytes]:
        symbol, start, end = self.symbol_file_range(name)
        return symbol, self.data[start:end]


@dataclasses.dataclass(frozen=True)
class Insn:
    op: str
    args: tuple[object, ...] = ()

    def json(self) -> dict[str, object]:
        return {"op": self.op, "args": list(self.args)}


@dataclasses.dataclass(frozen=True)
class Decoded:
    insn: Insn
    start: int
    end: int


class Reader:
    def __init__(self, code: bytes) -> None:
        self.code = code
        self.offset = 0

    def remaining(self) -> int:
        return len(self.code) - self.offset

    def take(self) -> int:
        if self.offset >= len(self.code):
            raise CheckError("truncated instruction")
        value = self.code[self.offset]
        self.offset += 1
        return value

    def peek(self) -> int:
        if self.offset >= len(self.code):
            raise CheckError("truncated instruction")
        return self.code[self.offset]

    def take_u32(self) -> int:
        if self.offset + 4 > len(self.code):
            raise CheckError("truncated imm32/disp32")
        value = struct.unpack_from("<I", self.code, self.offset)[0]
        self.offset += 4
        return value

    def take_i32(self) -> int:
        value = self.take_u32()
        return value - (1 << 32) if value >= (1 << 31) else value

    def take_i8(self) -> int:
        value = self.take()
        return value - 256 if value >= 128 else value



def bits(value: int, start: int, width: int) -> int:
    return (value >> start) & ((1 << width) - 1)


def invbit(value: int, index: int) -> int:
    return 1 - bits(value, index, 1)


def gpr_name(number: int) -> str:
    if not 0 <= number < 16:
        raise CheckError(f"invalid GPR {number}")
    return GPRS[number]


def decode_address(reader: Reader, modrm: int, base_extension: int, tuple_scale: int = 1) -> tuple[str, int]:
    mode = bits(modrm, 6, 2)
    rm = bits(modrm, 0, 3)
    if rm == 4:
        raise CheckError("SIB addressing is outside transpose proof vocabulary")
    if mode == 0 and rm == 5:
        raise CheckError("RIP-relative addressing is outside transpose proof vocabulary")
    base = gpr_name(rm + 8 * base_extension)
    if mode == 0:
        displacement = 0
    elif mode == 1:
        displacement = reader.take_i8() * tuple_scale
    elif mode == 2:
        displacement = reader.take_i32()
    else:
        raise CheckError("register addressing where memory was required")
    if displacement < 0:
        raise CheckError("negative displacement outside certified leaves")
    return base, displacement


def decode_one(reader: Reader) -> Decoded:
    start = reader.offset
    first = reader.take()

    if first == 0xC3:
        return Decoded(Insn("ret"), start, reader.offset)
    if first == 0xB8:
        return Decoded(Insn("movImm32", ("rax", reader.take_u32())), start, reader.offset)
    if first in (0x48, 0x4C):
        rex = first
        opcode = reader.take()
        modrm = reader.take()
        mode = bits(modrm, 6, 2)
        reg = bits(modrm, 3, 3) + 8 * bits(rex, 2, 1)
        rm = bits(modrm, 0, 3) + 8 * bits(rex, 0, 1)
        if opcode == 0x89 and mode == 3:
            return Decoded(Insn("movReg64", (gpr_name(rm), gpr_name(reg))), start, reader.offset)
        if opcode == 0x8B and mode != 3:
            # All pointer-table loads use unextended RSI as the base.  Decode
            # generically, but preserve the architectural read-before-write order.
            base, displacement = decode_address(reader, modrm, bits(rex, 0, 1))
            return Decoded(Insn("movLoad64", (gpr_name(reg), base, displacement)), start, reader.offset)
        raise CheckError(f"unsupported REX instruction at {start:#x}")

    if first == 0xC5:
        p1 = reader.take()
        opcode = reader.take()
        # VZEROUPPER is the only no-ModRM VEX instruction.
        if p1 == 0xF8 and opcode == 0x77:
            return Decoded(Insn("vzeroUpper"), start, reader.offset)
        modrm = reader.take()
        mode = bits(modrm, 6, 2)
        if opcode == 0x92:
            # VEX.128.66.0F.W0 KMOVB k, r32.
            if p1 != 0xF9 or mode != 3:
                raise CheckError("invalid KMOVB form")
            kreg = bits(modrm, 3, 3)
            source = gpr_name(bits(modrm, 0, 3))
            return Decoded(Insn("kmovb", (kreg, source)), start, reader.offset)
        r_ext = invbit(p1, 7)
        source1 = 15 - bits(p1, 3, 4)
        vector_length = bits(p1, 2, 1)
        pp = bits(p1, 0, 2)
        if vector_length != 1:
            raise CheckError("transpose VEX instruction is not 256-bit")
        destination = bits(modrm, 3, 3) + 8 * r_ext
        if opcode in (0x6C, 0x6D):
            if mode != 3 or pp != 1:
                raise CheckError("invalid VPUNPCKQDQ form")
            source2 = bits(modrm, 0, 3)
            op = "unpackLow" if opcode == 0x6C else "unpackHigh"
            return Decoded(Insn(op, (destination, source1, source2)), start, reader.offset)
        if opcode in (0x6F, 0x7F):
            if pp != 2 or bits(p1, 3, 4) != 15:
                raise CheckError("invalid VMOVDQU prefix/reserved vvvv")
            if mode == 3:
                raise CheckError("register VMOVDQU is outside proof vocabulary")
            base, displacement = decode_address(reader, modrm, 0)
            op = "ymmLoad" if opcode == 0x6F else "ymmStore"
            args = (destination, base, displacement) if op == "ymmLoad" else (base, displacement, destination)
            return Decoded(Insn(op, args), start, reader.offset)
        raise CheckError(f"unsupported two-byte VEX opcode {opcode:#x} at {start:#x}")

    if first == 0xC4:
        p0 = reader.take()
        p1 = reader.take()
        opcode = reader.take()
        modrm = reader.take()
        mode = bits(modrm, 6, 2)
        map_select = bits(p0, 0, 5)
        r_ext = invbit(p0, 7)
        b_ext = invbit(p0, 5)
        vector_length = bits(p1, 2, 1)
        pp = bits(p1, 0, 2)
        if (opcode != 0x6F or map_select != 1 or vector_length != 1 or pp != 2 or
                mode == 3 or bits(p1, 7, 1) != 0 or bits(p1, 3, 4) != 15 or
                bits(p0, 6, 1) != 1):
            raise CheckError(f"unsupported three-byte VEX instruction at {start:#x}")
        destination = bits(modrm, 3, 3) + 8 * r_ext
        base, displacement = decode_address(reader, modrm, b_ext)
        return Decoded(Insn("ymmLoad", (destination, base, displacement)), start, reader.offset)

    if first == 0x62:
        p0 = reader.take()
        p1 = reader.take()
        p2 = reader.take()
        opcode = reader.take()
        modrm = reader.take()
        mode = bits(modrm, 6, 2)
        map_select = bits(p0, 0, 3)
        destination = bits(modrm, 3, 3) + 8 * invbit(p0, 7) + 16 * invbit(p0, 4)
        source1 = (15 - bits(p1, 3, 4)) + 16 * invbit(p2, 3)
        b_ext = invbit(p0, 5)
        vl = bits(p2, 5, 2)
        zeroing = bool(bits(p2, 7, 1))
        broadcast = bool(bits(p2, 4, 1))
        mask = bits(p2, 0, 3)
        w = bits(p1, 7, 1)
        pp = bits(p1, 0, 2)
        if opcode == 0x43:
            if (mode != 3 or map_select != 3 or bits(p0, 3, 1) != 0 or
                    w != 1 or pp != 1 or vl != 1 or zeroing or broadcast or mask != 0):
                raise CheckError("invalid unmasked EVEX.256 VSHUFI64X2")
            source2 = bits(modrm, 0, 3) + 8 * invbit(p0, 6) + 16 * invbit(p0, 5)
            immediate = reader.take()
            return Decoded(Insn("shuffleI64x2", (destination, source1, source2, immediate)), start, reader.offset)
        if opcode == 0x6F:
            if (mode == 3 or map_select != 1 or bits(p0, 3, 1) != 0 or
                    bits(p0, 6, 1) != 1 or w != 1 or pp != 2 or vl != 1 or broadcast):
                raise CheckError("invalid EVEX.256 VMOVDQU64 load")
            if source1 != 0:
                # Reserved vvvv/V' must encode all ones, which decodes to zero
                # through the arithmetic above only after inversion.
                raise CheckError("reserved EVEX vvvv fields are not all ones")
            base, displacement = decode_address(reader, modrm, b_ext, tuple_scale=32)
            return Decoded(
                Insn("ymmMaskedLoad", (destination, base, displacement, mask, zeroing)),
                start,
                reader.offset,
            )
        raise CheckError(f"unsupported EVEX opcode {opcode:#x} at {start:#x}")

    raise CheckError(f"unsupported opcode byte {first:#x} at {start:#x}")


def decode(code: bytes) -> list[Decoded]:
    reader = Reader(code)
    result: list[Decoded] = []
    while reader.remaining():
        item = decode_one(reader)
        result.append(item)
        if item.insn.op == "ret":
            if reader.remaining():
                raise CheckError("bytes follow RET inside function symbol")
            break
    if not result or result[-1].insn.op != "ret":
        raise CheckError("function does not end in RET")
    return result


SHUFFLE_BLOCK = (
    Insn("unpackLow", (4, 0, 1)),
    Insn("unpackHigh", (5, 0, 1)),
    Insn("unpackLow", (6, 2, 3)),
    Insn("unpackHigh", (7, 2, 3)),
    Insn("shuffleI64x2", (0, 4, 6, 0)),
    Insn("shuffleI64x2", (1, 5, 7, 0)),
    Insn("shuffleI64x2", (2, 4, 6, 3)),
    Insn("shuffleI64x2", (3, 5, 7, 3)),
)

POINTER_SETUP = (
    Insn("movReg64", ("rax", "rdi")),
    Insn("movLoad64", ("rdx", "rsi", 0)),
    Insn("movLoad64", ("rcx", "rsi", 8)),
    Insn("movLoad64", ("r8", "rsi", 16)),
    Insn("movLoad64", ("r9", "rsi", 24)),
    Insn("movLoad64", ("r10", "rsi", 32)),
    Insn("movLoad64", ("r11", "rsi", 40)),
    Insn("movLoad64", ("rdi", "rsi", 48)),
    Insn("movLoad64", ("rsi", "rsi", 56)),
)

FIRST_HALF = ("rdx", "rcx", "r8", "r9")
SECOND_HALF = ("r10", "r11", "rdi", "rsi")


def projective_half(source_offset: int, lane_half: int, pointers: Sequence[str]) -> tuple[Insn, ...]:
    loads = tuple(Insn("ymmLoad", (index, pointer, source_offset)) for index, pointer in enumerate(pointers))
    stores = tuple(
        Insn("ymmStore", ("rax", coordinate * 320 + 2 * source_offset + lane_half, coordinate))
        for coordinate in range(4)
    )
    return loads + SHUFFLE_BLOCK + stores


def affine_half(source_offset: int, output_offset: int, pointers: Sequence[str]) -> tuple[Insn, ...]:
    loads = tuple(
        Insn("ymmMaskedLoad", (index, pointer, source_offset, 1, True))
        for index, pointer in enumerate(pointers)
    )
    stores = tuple(
        Insn("ymmStore", ("rax", coordinate * 320 + output_offset, coordinate))
        for coordinate in range(3)
    )
    return loads + SHUFFLE_BLOCK + stores


def expected_projective() -> tuple[Insn, ...]:
    body: list[Insn] = list(POINTER_SETUP)
    for limb in range(5):
        offset = 32 * limb
        body.extend(projective_half(offset, 0, FIRST_HALF))
        body.extend(projective_half(offset, 32, SECOND_HALF))
    body.extend((Insn("vzeroUpper"), Insn("ret")))
    return tuple(body)


def expected_affine() -> tuple[Insn, ...]:
    body: list[Insn] = [Insn("movImm32", ("rax", 7)), Insn("kmovb", (1, "rax")), *POINTER_SETUP]
    for limb in range(5):
        source_offset = 24 * limb
        output_offset = 64 * limb
        body.extend(affine_half(source_offset, output_offset, FIRST_HALF))
        body.extend(affine_half(source_offset, output_offset + 32, SECOND_HALF))
    body.extend((Insn("vzeroUpper"), Insn("ret")))
    return tuple(body)


def compare_program(name: str, actual: Sequence[Decoded], expected: Sequence[Insn]) -> None:
    actual_insns = [item.insn for item in actual]
    if len(actual_insns) != len(expected):
        raise CheckError(f"{name}: instruction count {len(actual_insns)} != {len(expected)}")
    for index, (got, want) in enumerate(zip(actual_insns, expected)):
        if got != want:
            start = actual[index].start
            raise CheckError(f"{name}: instruction {index} at {start:#x}: {got} != {want}")


def qword_ranges(base: tuple[str, int], count: int) -> set[tuple[str, int]]:
    kind, source = base
    return {(kind, source + 8 * lane) for lane in range(count)}


def certify_layout(name: str, program: Sequence[Insn], affine: bool) -> dict[str, object]:
    # Symbolically bind the eight post-prelude pointer registers to source ids.
    gpr: dict[str, tuple[str, int]] = {
        "rdi": ("out", 0), "rsi": ("pointerTable", 0), "rsp": ("stack", 0)
    }
    ymm: dict[int, tuple[object, object, object, object]] = {}
    output: dict[int, object] = {}
    required_reads: set[tuple[str, int]] = set()
    required_writes: set[int] = set()
    kregs: dict[int, int] = {}
    returned = False

    def add_address(base: tuple[str, int], displacement: int) -> tuple[str, int]:
        return base[0], base[1] + displacement

    def load_pointer(address: tuple[str, int]) -> tuple[str, int]:
        if address[0] != "pointerTable" or address[1] % 8 or not 0 <= address[1] < 64:
            raise CheckError(f"{name}: invalid pointer-table read {address}")
        required_reads.update(qword_ranges(address, 1))
        return "source", address[1] // 8

    for index, insn in enumerate(program):
        op, args = insn.op, insn.args
        if op == "movImm32":
            target, value = args
            gpr[str(target)] = ("constant", int(value))
        elif op == "kmovb":
            target, source = args
            value = gpr.get(str(source))
            if value is None or value[0] != "constant":
                raise CheckError(f"{name}: KMOVB source is not a known constant")
            kregs[int(target)] = value[1] & 0xFF
        elif op == "movReg64":
            target, source = args
            if str(source) not in gpr:
                raise CheckError(f"{name}: unbound GPR {source}")
            gpr[str(target)] = gpr[str(source)]
        elif op == "movLoad64":
            target, base, displacement = args
            if str(base) not in gpr:
                raise CheckError(f"{name}: unbound address GPR {base}")
            address = add_address(gpr[str(base)], int(displacement))
            value = load_pointer(address)
            gpr[str(target)] = value
        elif op in ("ymmLoad", "ymmMaskedLoad"):
            if op == "ymmLoad":
                destination, base, displacement = args
                active = (True, True, True, True)
            else:
                destination, base, displacement, mask_reg, zeroing = args
                mask_value = kregs.get(int(mask_reg))
                if mask_value is None:
                    raise CheckError(f"{name}: masked load uses unset k{mask_reg}")
                if not bool(zeroing):
                    raise CheckError(f"{name}: affine load must use zeroing")
                active = tuple(bool(mask_value & (1 << lane)) for lane in range(4))
            if str(base) not in gpr or gpr[str(base)][0] != "source":
                raise CheckError(f"{name}: load base {base} is not a source pointer")
            source = gpr[str(base)][1]
            row: list[object] = []
            for lane, enabled in enumerate(active):
                offset = int(displacement) + 8 * lane
                if enabled:
                    required_reads.add((f"source{source}", offset))
                    if affine and offset + 8 > 120:
                        raise CheckError(f"{name}: active affine read crosses 120-byte source: {source=} {offset=}")
                    limit = 120 if affine else 160
                    if offset + 8 > limit:
                        raise CheckError(f"{name}: source read crosses object: {source=} {offset=}")
                    row.append((source, offset // (24 if affine else 32), lane))
                else:
                    row.append(0 if zeroing else ("old", int(destination), lane))
            ymm[int(destination)] = tuple(row)  # type: ignore[assignment]
        elif op == "unpackLow":
            destination, a, b = map(int, args)
            aa, bb = ymm[a], ymm[b]
            ymm[destination] = (aa[0], bb[0], aa[2], bb[2])
        elif op == "unpackHigh":
            destination, a, b = map(int, args)
            aa, bb = ymm[a], ymm[b]
            ymm[destination] = (aa[1], bb[1], aa[3], bb[3])
        elif op == "shuffleI64x2":
            destination, a, b, immediate = map(int, args)
            aa, bb = ymm[a], ymm[b]
            astart = 2 if immediate & 1 else 0
            bstart = 2 if immediate & 2 else 0
            ymm[destination] = (aa[astart], aa[astart + 1], bb[bstart], bb[bstart + 1])
        elif op == "ymmStore":
            base, displacement, source = args
            if str(base) not in gpr or gpr[str(base)] != ("out", 0):
                raise CheckError(f"{name}: store base does not preserve original output pointer")
            row = ymm[int(source)]
            for lane, value in enumerate(row):
                byte = int(displacement) + 8 * lane
                if byte in output:
                    raise CheckError(f"{name}: duplicate output qword at {byte}")
                output[byte] = value
                required_writes.add(byte)
        elif op == "vzeroUpper":
            pass
        elif op == "ret":
            if index != len(program) - 1:
                raise CheckError(f"{name}: RET is not last")
            returned = True
        else:
            raise CheckError(f"{name}: unsupported semantic instruction {insn}")

    if not returned:
        raise CheckError(f"{name}: no RET")
    coordinates = 3 if affine else 4
    expected_qwords = coordinates * 5 * 8
    if len(output) != expected_qwords:
        raise CheckError(f"{name}: output coverage {len(output)} != {expected_qwords}")
    for coordinate in range(coordinates):
        for limb in range(5):
            for lane in range(8):
                byte = coordinate * 320 + limb * 64 + lane * 8
                value = output.get(byte)
                source_row_width = 3 if affine else 4
                expected_value = (lane, limb, coordinate)
                # The symbolic token's third component is source qword/coordinate.
                if value != expected_value:
                    raise CheckError(
                        f"{name}: output ({coordinate},{limb},{lane}) at {byte} = {value}, expected {expected_value}"
                    )
    expected_bytes = coordinates * 320
    if required_writes != set(range(0, expected_bytes, 8)):
        raise CheckError(f"{name}: output qword frame is not exactly 0..{expected_bytes}")

    guard_page_suppression = None
    if affine:
        # Prove at executable-checker level that the only qwords needed from a
        # source are offsets 0..112.  In particular source+120 is absent even
        # for the final row at displacement 96.
        source_offsets = sorted({offset for kind, offset in required_reads if kind.startswith("source")})
        if source_offsets != list(range(0, 120, 8)):
            raise CheckError(f"affine active source read set changed: {source_offsets}")
        if any((f"source{source}", 120) in required_reads for source in range(8)):
            raise CheckError("affine masked-off fourth qword was treated as readable")
        guard_page_suppression = True

    return {
        "instruction_count": len(program),
        "output_bytes": expected_bytes,
        "output_qwords": expected_qwords,
        "required_read_qwords": len(required_reads),
        "required_write_qwords": len(required_writes),
        "affine_masked_tail_fault_suppressed": guard_page_suppression,
    }


def check_object(path: Path, symbol_name: str, expected: Sequence[Insn], affine: bool) -> dict[str, object]:
    elf = Elf(path.read_bytes())
    symbol, code = elf.symbol_bytes(symbol_name)
    decoded = decode(code)
    compare_program(symbol_name, decoded, expected)
    layout = certify_layout(symbol_name, [item.insn for item in decoded], affine)
    return {
        "path": str(path),
        "symbol": symbol_name,
        "symbol_size": symbol.size,
        "symbol_sha256": hashlib.sha256(code).hexdigest(),
        "relocations": [],
        **layout,
        "program": [item.insn.json() for item in decoded],
        "instruction_offsets": [[item.start, item.end] for item in decoded],
    }


def run(projective: Path, affine: Path) -> dict[str, object]:
    projective_report = check_object(projective, PROJECTIVE_SYMBOL, expected_projective(), False)
    affine_report = check_object(affine, AFFINE_SYMBOL, expected_affine(), True)
    return {
        "schema": "narya.transpose-whole-leaf-object-trace.v1",
        "projective": projective_report,
        "affine": affine_report,
        "claims": {
            "exact_relocation_free_symbol_bytes_checked": True,
            "gpr_pointer_setup_checked": True,
            "source_load_offsets_checked": True,
            "affine_mask_and_zeroing_checked": True,
            "affine_masked_off_qword_read_permission_not_required": True,
            "shuffle_network_checked": True,
            "output_offsets_and_lane_map_checked": True,
            "vzeroupper_ret_checked": True,
            "physical_cpu_correctness": False,
            "downstream_binary_identity": False,
        },
    }


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser()
    parser.add_argument("--projective", type=Path, default=root / "build/proof/projective_niels_transpose_x8.o")
    parser.add_argument("--affine", type=Path, default=root / "build/proof/affine_niels_transpose_x8.o")
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = run(args.projective, args.affine)
    rendered = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    if args.json:
        print(rendered, end="")
    else:
        p = report["projective"]
        a = report["affine"]
        print(f"OK: projective whole leaf: {p['symbol_size']} bytes, {p['instruction_count']} instructions")
        print(f"OK: affine whole leaf: {a['symbol_size']} bytes, {a['instruction_count']} instructions")
        print("OK: affine K1=0b0111 zero-masked loads require no permission for qword 4")
        print("OK: exact output lane maps, byte frames, VZEROUPPER, and RET are pinned")


if __name__ == "__main__":
    try:
        main()
    except CheckError as error:
        raise SystemExit(f"transpose object refinement failed: {error}")
