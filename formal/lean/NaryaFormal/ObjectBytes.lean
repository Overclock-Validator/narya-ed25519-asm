/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Kernel-reduced sanity properties of the canonical linked multiplier image.
This file establishes that the generated literals are well-formed bytes and
that the resolved read-only constants have their claimed integer values. It
does not yet decode symbolBytes or give them x86 execution semantics.
-/

import NaryaFormal.GeneratedR51ObjectBytes

namespace NaryaFormal.R51Object

def littleEndianNat : List Nat → Nat
  | [] => 0
  | byte :: rest => byte + 256 * littleEndianNat rest

set_option maxRecDepth 4096 in
theorem symbol_extent_exact :
    symbolBytes.length = symbolSize := by decide

set_option maxRecDepth 4096 in
theorem symbol_bytes_are_octets :
    ∀ byte ∈ symbolBytes, byte < 256 := by decide

theorem constant_extents_exact :
    ifma_mask51Bytes.length = 8 ∧ ifma_fold19Bytes.length = 8 ∧
      ifma_sub_bias0Bytes.length = 8 ∧ ifma_sub_biasnBytes.length = 8 := by
  decide

theorem resolved_constants_correct :
    littleEndianNat ifma_mask51Bytes = 2 ^ 51 - 1 ∧
      littleEndianNat ifma_fold19Bytes = 19 ∧
      littleEndianNat ifma_sub_bias0Bytes = 4 * (2 ^ 51 - 19) ∧
      littleEndianNat ifma_sub_biasnBytes = 4 * (2 ^ 51 - 1) := by
  decide

end NaryaFormal.R51Object
