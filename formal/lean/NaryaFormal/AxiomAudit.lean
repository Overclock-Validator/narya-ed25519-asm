/-
Axiom audit for the capstone theorems.

Each check fails the build if the theorem's axioms change. The capstones use
only Lean's three standard axioms: no `sorryAx`, and no `Lean.ofReduceBool`
(which `native_decide` and `bv_decide` would add, extending trust to the
compiler and native code). A new capstone should be added here.
-/
import NaryaFormal.X86GoR51MulReflective
import NaryaFormal.X86GoR51NormalizeReflective
import NaryaFormal.X86GoR51AddReflective
import NaryaFormal.X86GoR51SubtractReflective
import NaryaFormal.X86GoR51NegateReflective
import NaryaFormal.X86R51MulReflective
import NaryaFormal.TransposeX86WholeSoundness
import NaryaFormal.X86EpilogueRefinement

/-- info: 'NaryaFormal.IfmaSym.GoR51Mul.go_r51_multiplier_refines_relocated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaryaFormal.IfmaSym.GoR51Mul.go_r51_multiplier_refines_relocated

/-- info: 'NaryaFormal.IfmaSym.GoR51Normalize.go_r51_normalize_refines_relocated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaryaFormal.IfmaSym.GoR51Normalize.go_r51_normalize_refines_relocated

/-- info: 'NaryaFormal.IfmaSym.GoR51Add.go_r51_add_refines_relocated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaryaFormal.IfmaSym.GoR51Add.go_r51_add_refines_relocated

/-- info: 'NaryaFormal.IfmaSym.GoR51Subtract.go_r51_subtract_refines_relocated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaryaFormal.IfmaSym.GoR51Subtract.go_r51_subtract_refines_relocated

/-- info: 'NaryaFormal.IfmaSym.GoR51Negate.go_r51_negate_refines_relocated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaryaFormal.IfmaSym.GoR51Negate.go_r51_negate_refines_relocated

/-- info: 'NaryaFormal.IfmaSym.R51Mul.r51_multiplier_reflective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaryaFormal.IfmaSym.R51Mul.r51_multiplier_reflective

/-- info: 'NaryaFormal.TransposeWholeX86.projective_whole_leaf_binary_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaryaFormal.TransposeWholeX86.projective_whole_leaf_binary_refines

/-- info: 'NaryaFormal.TransposeWholeX86.affine_whole_leaf_binary_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaryaFormal.TransposeWholeX86.affine_whole_leaf_binary_refines

/-- info: 'NaryaFormal.X86.run_r51_multiplier_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms NaryaFormal.X86.run_r51_multiplier_refines
