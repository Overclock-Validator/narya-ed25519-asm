/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Checks the executable specification against the committed fixtures in
tests/vectors. None of these fixtures were produced by this code: they come
from RFC 8032, C2SP CCTV, Wycheproof, Go's crypto/ed25519 oracle and the
repository's Python affine big-integer generators.

Usage:
  narya-spec-check [VECTORS_DIRECTORY]
  narya-spec-check --verdicts FILE.jsonl   (any file in the external schema)
-/

import Lean.Data.Json
import NaryaSpec

open NaryaSpec

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def hexPairs? : List Char → Option (List UInt8)
  | [] => some []
  | [_] => none
  | high :: low :: rest => do
      let h ← hexDigit? high
      let l ← hexDigit? low
      let tail ← hexPairs? rest
      pure ((h * 16 + l).toUInt8 :: tail)

def hexBytes? (s : String) : Option ByteArray :=
  (hexPairs? s.toList).map fun bytes => ⟨bytes.toArray⟩

/-- Big-endian hexadecimal integer, as the decode fixture writes limbs. -/
def hexNat? (s : String) : Option Nat :=
  s.toList.foldlM (fun acc c => (hexDigit? c).map (acc * 16 + ·)) 0

def toHex (bytes : ByteArray) : String :=
  String.join (bytes.toList.map fun b =>
    let digits := "0123456789abcdef".toList
    String.mk [digits[b.toNat / 16]!, digits[b.toNat % 16]!])

def sameBytes (a b : ByteArray) : Bool := a.data == b.data

/-- Fixture lines without comments or blanks, split on spaces. -/
def fixtureRows (path : System.FilePath) : IO (Array (List String)) := do
  let lines ← IO.FS.lines path
  pure <| lines.filterMap fun line =>
    let line := line.trim
    if line.isEmpty || line.startsWith "#" then none
    else some ((line.splitOn " ").filter (· ≠ ""))

structure Tally where
  passed : Nat := 0
  failed : Nat := 0
  shown : Nat := 0

def Tally.record (t : Tally) (ok : Bool) (detail : Unit → String) : IO Tally := do
  if ok then
    pure { t with passed := t.passed + 1 }
  else
    if t.shown < 5 then IO.eprintln s!"  mismatch: {detail ()}"
    pure { t with failed := t.failed + 1, shown := t.shown + 1 }

def Tally.report (t : Tally) (name : String) (expected : Option Nat := none) : IO Bool := do
  let countOk := match expected with
    | some n => t.passed + t.failed = n
    | none => t.passed + t.failed > 0
  let ok := t.failed = 0 && countOk
  IO.println s!"{if ok then "PASS" else "FAIL"}: {name}: {t.passed}/{t.passed + t.failed}"
  pure ok

def B := Point.basepoint

def checkSha512 : IO Bool := do
  let cases : List (String × String) := [
    ("", "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce" ++
      "47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e"),
    ("abc", "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a" ++
      "2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f"),
    ("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" ++
      "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu",
      "8e959b75dae313da8cf4f72814fc143f8f7779c6eb9f7fa17299aeadb6889018" ++
      "501d289e4900f7e4331b99dec4b5433ac7d329eeb6dd26545e96e55b874be909")]
  let mut t : Tally := {}
  for (message, digest) in cases do
    let got := toHex (Sha512.hash message.toUTF8)
    t ← t.record (got == digest) fun _ => s!"sha512 {message.length} bytes: {got}"
  t.report "SHA-512 FIPS 180-4 examples" (some 3)

def checkCurve : IO Bool := do
  let mut t : Tally := {}
  let encoded := "5866666666666666666666666666666666666666666666666666666666666666"
  t ← t.record B.onCurve fun _ => "basepoint not on curve"
  t ← t.record (toHex B.encode == encoded) fun _ => "basepoint encoding"
  t ← t.record ((hexBytes? encoded).bind Point.decode == some B) fun _ => "basepoint decode"
  t ← t.record (Point.nsmul L B == Point.identity) fun _ => "[L]B is not the identity"
  t ← t.record (Point.nsmul (L - 1) B == B.neg) fun _ => "[L-1]B is not -B"
  -- Extended-coordinate multiples against the affine law.
  let scalars := (List.range 40) ++ [L - 1, L, L + 1, 2 ^ 253 - 1, 8 * L - 1,
    0x1d0f2e4a6b8c9d3e5f7a1b2c3d4e5f60718293a4b5c6d7e8f9a0b1c2d3e4f5a6]
  for n in scalars do
    t ← t.record (Point.nsmul n B == Point.nsmulAffine n B) fun _ => s!"ext/affine differ at {n}"
  t.report "curve constants and extended/affine agreement"

def checkBasepointMultiples (dir : System.FilePath) : IO Bool := do
  let mut t : Tally := {}
  let mut running := Point.identity
  for row in ← fixtureRows (dir / "narya_basepoint_multiples_v1.txt") do
    match row with
    | [n, hex] =>
        running := running.add B
        let n := n.toNat!
        t ← t.record (toHex (Point.nsmul n B).encode == hex && toHex running.encode == hex)
          fun _ => s!"[{n}]B"
    | _ => t ← t.record false fun _ => s!"bad row {row}"
  t.report "basepoint multiples [1]B..[128]B" (some 128)

def checkFixedBase (dir : System.FilePath) : IO Bool := do
  let mut t : Tally := {}
  for row in ← fixtureRows (dir / "narya_fixed_base_scalar_v1.txt") do
    match row with
    | [_, _, scalar, expected] =>
        let s := leNat ((hexBytes? scalar).getD .empty)
        t ← t.record (toHex (Point.nsmul s B).encode == expected) fun _ => s!"[{scalar}]B"
    | _ => t ← t.record false fun _ => s!"bad row {row}"
  t.report "fixed-base scalar multiples" (some 256)

def checkVariableBase (dir : System.FilePath) : IO Bool := do
  let mut t : Tally := {}
  for row in ← fixtureRows (dir / "narya_variable_scalar_mult_v1.txt") do
    match row with
    | [_, _, base, scalar, negative, expected] =>
        let s := leNat ((hexBytes? scalar).getD .empty)
        let product := Point.nsmul s (Point.nsmul base.toNat! B)
        let result := if negative == "1" then product.neg else product
        t ← t.record (toHex result.encode == expected) fun _ => s!"{base} {scalar} {negative}"
    | _ => t ← t.record false fun _ => s!"bad row {row}"
  t.report "variable-base signed scalar multiples" (some 256)

/-- Radix-2^51 limbs, least significant first, to a residue. -/
def limbsValue (limbs : List String) : Nat :=
  (limbs.zip (List.range 5)).foldl
    (fun acc (limb, i) => acc + (hexNat? limb).getD 0 * 2 ^ (51 * i)) 0

def checkPermissiveDecode (dir : System.FilePath) : IO Bool := do
  let mut t : Tally := {}
  for row in ← fixtureRows (dir / "narya_permissive_decode_v1.txt") do
    match row with
    | input :: valid :: coords =>
        let decoded := (hexBytes? input).bind Point.decode
        if valid == "1" && coords.length == 20 then
          let X := Fe.ofNat (limbsValue (coords.take 5))
          let Y := Fe.ofNat (limbsValue ((coords.drop 5).take 5))
          let Z := Fe.ofNat (limbsValue ((coords.drop 10).take 5))
          let zInv := Fe.inv Z
          t ← t.record (decoded == some ⟨X * zInv, Y * zInv⟩) fun _ => s!"decode {input}"
        else
          t ← t.record (valid == "0" && decoded.isNone) fun _ => s!"reject {input}"
    | _ => t ← t.record false fun _ => s!"bad row {row}"
  t.report "permissive decoder decisions and coordinates" (some 256)

def checkScalarReduction (dir : System.FilePath) : IO Bool := do
  let mut t : Tally := {}
  let text ← IO.FS.readFile (dir / "narya_scalar_reduction_adversarial_v1.json")
  match Lean.Json.parse text >>= (·.getObjVal? "vectors") >>= (·.getArr?) with
  | .error e => IO.eprintln s!"  scalar fixture: {e}"; t ← t.record false fun _ => "parse"
  | .ok vectors =>
      for v in vectors do
        let input := (v.getObjValAs? String "input_64_le_hex").toOption.bind hexBytes?
        let expected := (v.getObjValAs? String "expected_integer_decimal").toOption.bind (·.toNat?)
        let expectedHex := (v.getObjValAs? String "expected_32_le_hex").toOption.getD ""
        match input, expected with
        | some bytes, some n =>
            t ← t.record (leNat bytes % L == n && toHex (natToLE n 32) == expectedHex)
              fun _ => s!"reduce {toHex bytes}"
        | _, _ => t ← t.record false fun _ => "bad vector"
  t.report "scalar reduction mod L" (some 31)

def checkStrictVerify (dir : System.FilePath) : IO Bool := do
  let mut t : Tally := {}
  for row in ← fixtureRows (dir / "narya_strict_verify_v1.txt") do
    match row with
    | [_, pub, sig, msg] =>
        let message := if msg == "-" then ByteArray.empty else (hexBytes? msg).getD .empty
        let ok := verifyStrict ((hexBytes? pub).getD .empty) message ((hexBytes? sig).getD .empty)
        t ← t.record ok fun _ => s!"valid signature rejected: {pub}"
    | _ => t ← t.record false fun _ => s!"bad row {row}"
  t.report "independently signed inputs, 0 to 4096 bytes" (some 8)

def jsonField? (line field : String) : Option String :=
  match line.splitOn ("\"" ++ field ++ "\":\"") with
  | _ :: rest :: _ => (rest.splitOn "\"").head?
  | _ => none

/-- Every record in the external-corpus schema; the verdict must match. -/
def checkVerdicts (path : System.FilePath) (expectedCount : Option Nat) : IO Bool := do
  let mut t : Tally := {}
  let mut accepted := 0
  let start ← IO.monoMsNow
  for line in ← IO.FS.lines path do
    if line.trim.isEmpty then continue
    let name := (jsonField? line "name").getD "?"
    let field (f : String) := (jsonField? line f).bind hexBytes?
    let expected := match line.splitOn "\"narya_dalek_strict\":" with
      | _ :: rest :: _ => if rest.startsWith "true" then some true
          else if rest.startsWith "false" then some false else none
      | _ => none
    match field "public_key", field "message", field "signature", expected with
    | some pub, some msg, some sig, some want =>
        let got := verifyStrict pub msg sig
        if got then accepted := accepted + 1
        t ← t.record (got == want) fun _ => s!"{name}: spec={got} expected={want}"
    | _, _, _, _ => t ← t.record false fun _ => s!"bad record {name}"
  let elapsed := (← IO.monoMsNow) - start
  let total := t.passed + t.failed
  IO.println s!"  {accepted} accepted, {total - accepted} rejected, {elapsed} ms ({if total = 0 then 0 else elapsed * 1000 / total} µs per verification)"
  t.report s!"DalekStrict verdicts in {path.fileName.getD ""}" expectedCount

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--verdicts", file] =>
      return if ← checkVerdicts file none then 0 else 1
  | _ =>
      let dir : System.FilePath := args.headD "../../tests/vectors"
      let results ← [checkSha512, checkCurve, checkBasepointMultiples dir,
        checkFixedBase dir, checkVariableBase dir, checkPermissiveDecode dir,
        checkScalarReduction dir, checkStrictVerify dir,
        checkVerdicts (dir / "narya_external_strict_v1.jsonl") (some 2954)].mapM id
      return if results.all id then 0 else 1
