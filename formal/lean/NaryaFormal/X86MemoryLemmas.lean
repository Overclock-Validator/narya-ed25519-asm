/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Permission and frame lemmas for the byte-addressed machine model that are
shared by the reflective leaf proofs.
-/

import NaryaFormal.X86Machine

namespace NaryaFormal.X86

theorem readableBytes_iff (memory : Memory) (base : Addr) (count : Nat) :
    readableBytes memory base count = true ↔
      ∀ offset, offset < count → (memory.perm (addressAdd base offset)).read = true := by
  simp [readableBytes, List.all_eq_true]


theorem writableBytes_iff (memory : Memory) (base : Addr) (count : Nat) :
    writableBytes memory base count = true ↔
      ∀ offset, offset < count → (memory.perm (addressAdd base offset)).write = true := by
  simp [writableBytes, List.all_eq_true]


theorem readableBytes_sub (memory : Memory) (base : Addr) (count offset size : Nat)
    (hread : readableBytes memory base count = true)
    (hbound : offset + size ≤ count) :
    readableBytes memory (addressAdd base offset) size = true := by
  rw [readableBytes_iff] at hread ⊢
  intro inner hinner
  rw [addressAdd_nested]
  exact hread _ (by omega)


theorem writableBytes_sub (memory : Memory) (base : Addr) (count offset size : Nat)
    (hwrite : writableBytes memory base count = true)
    (hbound : offset + size ≤ count) :
    writableBytes memory (addressAdd base offset) size = true := by
  rw [writableBytes_iff] at hwrite ⊢
  intro inner hinner
  rw [addressAdd_nested]
  exact hwrite _ (by omega)


theorem readableBytes_of_perm (memory other : Memory) (base : Addr) (count : Nat)
    (hperm : other.perm = memory.perm) :
    readableBytes other base count = readableBytes memory base count := by
  simp only [readableBytes, hperm]


theorem writableBytes_of_perm (memory other : Memory) (base : Addr) (count : Nat)
    (hperm : other.perm = memory.perm) :
    writableBytes other base count = writableBytes memory base count := by
  simp only [writableBytes, hperm]


/-- A little-endian qword depends only on its eight bytes. -/
theorem loadQwordLE_congr (memory other : Memory) (base : Addr)
    (hbytes : ∀ offset, offset < 8 →
      memory.byte (addressAdd base offset) = other.byte (addressAdd base offset)) :
    loadQwordLE memory base = loadQwordLE other base := by
  unfold loadQwordLE
  congr 1
  apply Finset.sum_congr rfl
  intro offset hoffset
  rw [hbytes offset (Finset.mem_range.mp hoffset)]


/-- A 64-byte ZMM store at `base+displacement` changes no byte outside
`[base, base+displacement+64)`. -/
theorem storeZmm_byte_outside (memory : Memory) (base : Addr)
    (displacement : Nat) (value : Zmm) (candidate : Addr)
    (houtside : ∀ offset, offset < displacement + 64 →
      candidate ≠ addressAdd base offset) :
    (storeZmm memory (addressAdd base displacement) value).byte candidate =
      memory.byte candidate := by
  apply storeZmm_frame
  simp only [zmmWrittenAddresses, qwordBytes, storeAddresses, addressAdd_nested,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or]
  repeat' apply And.intro
  all_goals exact houtside _ (by omega)


/-- Distinct in-range offsets from literal bases give distinct addresses. -/
theorem addressAdd_ofNat_ne (left right leftOffset rightOffset : Nat)
    (hne : left + leftOffset ≠ right + rightOffset)
    (hleft : left + leftOffset < 2 ^ 64) (hright : right + rightOffset < 2 ^ 64) :
    addressAdd (BitVec.ofNat 64 left) leftOffset ≠
      addressAdd (BitVec.ofNat 64 right) rightOffset := by
  intro hequal
  have hnat := congrArg BitVec.toNat hequal
  simp only [addressAdd, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.add_mod_mod,
    Nat.mod_add_mod] at hnat
  omega

end NaryaFormal.X86
