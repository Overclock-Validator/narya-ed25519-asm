/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Compositional refinement spine for the strict verifier.

This file intentionally states the complete theorem before all native leaves
have been refined. Each hypothesis is a named proof obligation. In
particular, `hLane` is the only place where eight-lane machine execution is
related to scalar verification; every protocol and group statement remains
scalar.

The point type is an additive group with its canonical integer action. It is
deliberately not a `ZMod L` module: DalekStrict admits mixed-order points, so
reducing a scalar modulo the prime subgroup order can change its action on the
torsion component.
-/

import Mathlib

namespace NaryaFormal.VerificationSpine

universe uBytes uMessage uDigest uPoint

/-- Fixed-width byte strings are abstract at this layer. Concrete byte-array
and length refinement belongs to the parser/wrapper obligations. -/
structure StrictInput
    (Bytes : Type uBytes) (Message : Type uMessage) where
  publicKeyBytes : Bytes
  signatureRBytes : Bytes
  signatureSBytes : Bytes
  message : Message

/-- Mathematical leaves used by the pure DalekStrict predicate. `decode` is
the permissive Edwards decoder and `hash` consumes the original R/A bytes. -/
structure StrictSpec
    (Bytes : Type uBytes) (Message : Type uMessage)
    (Digest : Type uDigest) (Point : Type uPoint) where
  order : ℕ
  basepoint : Point
  scalarValue : Bytes → ℕ
  decode : Bytes → Option Point
  encode : Point → Bytes
  hash : Bytes → Bytes → Message → Digest
  reduce : Digest → ℕ

/-- Implementation-facing leaves. Boolean predicates remain separate so the
top theorem records exactly which native comparisons require refinement. -/
structure StrictImplementation
    (Bytes : Type uBytes) (Message : Type uMessage)
    (Digest : Type uDigest) (Point : Type uPoint) where
  scalarValue : Bytes → ℕ
  scalarCanonical : Bytes → Bool
  decode : Bytes → Option Point
  smallOrder : Point → Bool
  canonicalR : Bytes → Point → Bool
  hash : Bytes → Bytes → Message → Digest
  reduce : Digest → ℕ
  equation : ℕ → ℕ → Point → Point → Bool

/-- Pure small order in the full Edwards group. On Edwards25519 the torsion
subgroup has order eight, so this is precisely `[8]P = O`. -/
def PureSmallOrder {Point : Type uPoint} [AddCommGroup Point]
    (point : Point) : Prop :=
  (8 : ℕ) • point = 0

/-- Cofactorless verification equation over the full group. Both scalar
actions are over the integers; no prime-order quotient is introduced. -/
def StrictEquation {Point : Type uPoint} [AddCommGroup Point]
    (basepoint : Point) (s k : ℕ) (publicKey signatureR : Point) : Prop :=
  (Int.ofNat s) • basepoint - (Int.ofNat k) • publicKey = signatureR

/-- Mathematical acceptance predicate corresponding to Narya's documented
DalekStrict profile. Canonical R is stated as an encode/decode round trip; in
the implementation it is equivalent to the terminal compressed-byte check. -/
def DalekStrict
    {Bytes : Type uBytes} {Message : Type uMessage}
    {Digest : Type uDigest} {Point : Type uPoint}
    [AddCommGroup Point]
    (spec : StrictSpec Bytes Message Digest Point)
    (input : StrictInput Bytes Message) : Prop :=
  spec.scalarValue input.signatureSBytes < spec.order ∧
    match spec.decode input.publicKeyBytes,
        spec.decode input.signatureRBytes with
    | some publicKey, some signatureR =>
        ¬PureSmallOrder publicKey ∧
        ¬PureSmallOrder signatureR ∧
        spec.encode signatureR = input.signatureRBytes ∧
        StrictEquation spec.basepoint
          (spec.scalarValue input.signatureSBytes)
          (spec.reduce (spec.hash input.signatureRBytes
            input.publicKeyBytes input.message))
          publicKey signatureR
    | _, _ => False

/-- Scalar implementation composition. The original encoded R/A values flow
directly into `hash`; decoded points are used only by point predicates and the
verification equation. -/
def verifyStrict
    {Bytes : Type uBytes} {Message : Type uMessage}
    {Digest : Type uDigest} {Point : Type uPoint}
    (impl : StrictImplementation Bytes Message Digest Point)
    (input : StrictInput Bytes Message) : Bool :=
  if impl.scalarCanonical input.signatureSBytes then
    match impl.decode input.publicKeyBytes,
        impl.decode input.signatureRBytes with
    | some publicKey, some signatureR =>
        if impl.smallOrder publicKey || impl.smallOrder signatureR then
          false
        else if impl.canonicalR input.signatureRBytes signatureR then
          impl.equation
            (impl.scalarValue input.signatureSBytes)
            (impl.reduce (impl.hash input.signatureRBytes
              input.publicKeyBytes input.message))
            publicKey signatureR
        else
          false
    | _, _ => false
  else
    false

/-- The leaf hypotheses form the typed audit scope. Once each commuting
square is discharged, scalar implementation acceptance is exactly the pure
predicate; rejecting every input cannot satisfy this `iff`. -/
theorem verifyStrict_correct
    {Bytes : Type uBytes} {Message : Type uMessage}
    {Digest : Type uDigest} {Point : Type uPoint}
    [AddCommGroup Point] [DecidableEq Bytes] [DecidableEq Point]
    (spec : StrictSpec Bytes Message Digest Point)
    (impl : StrictImplementation Bytes Message Digest Point)
    (hScalarValue : ∀ bytes, impl.scalarValue bytes = spec.scalarValue bytes)
    (hScalarCanonical : ∀ bytes,
      impl.scalarCanonical bytes = true ↔
        spec.scalarValue bytes < spec.order)
    (hDecode : ∀ bytes, impl.decode bytes = spec.decode bytes)
    (hSmallOrder : ∀ point,
      impl.smallOrder point = true ↔ PureSmallOrder point)
    (hCanonicalR : ∀ bytes point,
      impl.canonicalR bytes point = true ↔ spec.encode point = bytes)
    (hHash : ∀ rBytes aBytes message,
      impl.hash rBytes aBytes message = spec.hash rBytes aBytes message)
    (hReduce : ∀ digest, impl.reduce digest = spec.reduce digest)
    (hEquation : ∀ s k publicKey signatureR,
      impl.equation s k publicKey signatureR = true ↔
        StrictEquation spec.basepoint s k publicKey signatureR)
    (input : StrictInput Bytes Message) :
    verifyStrict impl input = true ↔ DalekStrict spec input := by
  have hSmallOrderFalse (point : Point) :
      impl.smallOrder point = false ↔ ¬PureSmallOrder point := by
    rw [Bool.eq_false_iff]
    exact not_congr (hSmallOrder point)
  cases hPublicKey : spec.decode input.publicKeyBytes with
  | none =>
      simp [verifyStrict, DalekStrict, hScalarCanonical, hDecode, hPublicKey]
  | some publicKey =>
      cases hSignatureR : spec.decode input.signatureRBytes with
      | none =>
          simp [verifyStrict, DalekStrict, hScalarCanonical, hDecode,
            hPublicKey, hSignatureR]
      | some signatureR =>
          simp [verifyStrict, DalekStrict, hScalarValue, hScalarCanonical,
            hDecode, hSmallOrder, hSmallOrderFalse, hCanonicalR, hHash,
            hReduce, hEquation,
            hPublicKey, hSignatureR, Bool.or_eq_true, not_or]
          tauto

/-- One SIMD group. Keeping this as a function makes lane identity explicit
and avoids duplicating all scalar protocol definitions eight times. -/
abbrev Lane8 (α : Type uBytes) := Fin 8 → α

/-- Native x8 composition theorem. All SIMD reasoning is quarantined in
`hLane`; the remaining hypotheses are the scalar commuting squares above. -/
theorem verifyStrictX8_correct
    {Bytes : Type uBytes} {Message : Type uMessage}
    {Digest : Type uDigest} {Point : Type uPoint}
    [AddCommGroup Point] [DecidableEq Bytes] [DecidableEq Point]
    (spec : StrictSpec Bytes Message Digest Point)
    (impl : StrictImplementation Bytes Message Digest Point)
    (native : Lane8 (StrictInput Bytes Message) → Lane8 Bool)
    (hLane : ∀ inputs lane,
      native inputs lane = verifyStrict impl (inputs lane))
    (hScalarValue : ∀ bytes, impl.scalarValue bytes = spec.scalarValue bytes)
    (hScalarCanonical : ∀ bytes,
      impl.scalarCanonical bytes = true ↔
        spec.scalarValue bytes < spec.order)
    (hDecode : ∀ bytes, impl.decode bytes = spec.decode bytes)
    (hSmallOrder : ∀ point,
      impl.smallOrder point = true ↔ PureSmallOrder point)
    (hCanonicalR : ∀ bytes point,
      impl.canonicalR bytes point = true ↔ spec.encode point = bytes)
    (hHash : ∀ rBytes aBytes message,
      impl.hash rBytes aBytes message = spec.hash rBytes aBytes message)
    (hReduce : ∀ digest, impl.reduce digest = spec.reduce digest)
    (hEquation : ∀ s k publicKey signatureR,
      impl.equation s k publicKey signatureR = true ↔
        StrictEquation spec.basepoint s k publicKey signatureR)
    (inputs : Lane8 (StrictInput Bytes Message)) (lane : Fin 8) :
    native inputs lane = true ↔ DalekStrict spec (inputs lane) := by
  rw [hLane]
  exact verifyStrict_correct spec impl hScalarValue hScalarCanonical hDecode
    hSmallOrder hCanonicalR hHash hReduce hEquation (inputs lane)

end NaryaFormal.VerificationSpine
