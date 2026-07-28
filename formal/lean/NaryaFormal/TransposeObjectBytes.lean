/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Kernel-reduced sanity properties of the two assembled transpose symbols.
These theorems establish artifact extent and byte well-formedness only. The
restricted opcode decoder and execution refinement remain separate work.
-/

import NaryaFormal.GeneratedTransposeObjectBytes

namespace NaryaFormal.TransposeObject

set_option maxRecDepth 16384 in
theorem projective_symbol_extent_exact :
    projectiveSymbolBytes.length = projectiveSymbolSize := by decide

set_option maxRecDepth 16384 in
theorem projective_symbol_bytes_are_octets :
    ∀ byte ∈ projectiveSymbolBytes, byte < 256 := by decide

set_option maxRecDepth 16384 in
theorem affine_symbol_extent_exact :
    affineSymbolBytes.length = affineSymbolSize := by decide

set_option maxRecDepth 16384 in
theorem affine_symbol_bytes_are_octets :
    ∀ byte ∈ affineSymbolBytes, byte < 256 := by decide

end NaryaFormal.TransposeObject
