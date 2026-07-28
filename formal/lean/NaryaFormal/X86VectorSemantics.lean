/-
Copyright 2026 Overclock Validator
SPDX-License-Identifier: Apache-2.0

Exact qword-lane semantics and no-wrap refinement lemmas for the restricted
AVX-512 subset used by the r51 multiplier. This file intentionally does not
decode instruction bytes, model memory, or define the complete machine state.
It is the reusable BitVec-to-Nat bridge consumed by that later proof.
-/

import Mathlib

namespace NaryaFormal.X86

abbrev QWord := BitVec 64
abbrev Zmm := Fin 8 → QWord

def U64 : Nat := 2 ^ 64
def U52 : Nat := 2 ^ 52
def B51 : Nat := 2 ^ 51

def src52 (x : QWord) : Nat := x.toNat % U52
def ifmaLo52 (x y : QWord) : Nat := (src52 x * src52 y) % U52
def ifmaHi52 (x y : QWord) : Nat := (src52 x * src52 y) / U52

def qwordAdd (x y : QWord) : QWord :=
  BitVec.ofNat 64 (x.toNat + y.toNat)

def qwordMul (x y : QWord) : QWord :=
  BitVec.ofNat 64 (x.toNat * y.toNat)

def qwordShiftLeft (x : QWord) (amount : Nat) : QWord :=
  BitVec.ofNat 64 (x.toNat * 2 ^ amount)

def qwordShiftRight (x : QWord) (amount : Nat) : QWord :=
  BitVec.ofNat 64 (x.toNat / 2 ^ amount)

def qwordMask51 (x : QWord) : QWord :=
  BitVec.ofNat 64 (x.toNat % B51)

def vpmadd52luqLane (acc x y : QWord) : QWord :=
  BitVec.ofNat 64 (acc.toNat + ifmaLo52 x y)

def vpmadd52huqLane (acc x y : QWord) : QWord :=
  BitVec.ofNat 64 (acc.toNat + ifmaHi52 x y)

def laneMap1 (operation : QWord → QWord) (x : Zmm) : Zmm :=
  fun lane => operation (x lane)

def laneMap2 (operation : QWord → QWord → QWord) (x y : Zmm) : Zmm :=
  fun lane => operation (x lane) (y lane)

def laneMap3 (operation : QWord → QWord → QWord → QWord)
    (x y z : Zmm) : Zmm :=
  fun lane => operation (x lane) (y lane) (z lane)

def vpmadd52luq (acc x y : Zmm) : Zmm :=
  laneMap3 vpmadd52luqLane acc x y

def vpmadd52huq (acc x y : Zmm) : Zmm :=
  laneMap3 vpmadd52huqLane acc x y

def vpaddq (x y : Zmm) : Zmm := laneMap2 qwordAdd x y
def vpmullq (x y : Zmm) : Zmm := laneMap2 qwordMul x y
def vpsllq (x : Zmm) (amount : Nat) : Zmm :=
  laneMap1 (fun value => qwordShiftLeft value amount) x
def vpsrlq (x : Zmm) (amount : Nat) : Zmm :=
  laneMap1 (fun value => qwordShiftRight value amount) x
def vpandMask51 (x : Zmm) : Zmm := laneMap1 qwordMask51 x

theorem qword_toNat_lt (x : QWord) : x.toNat < U64 := by
  simpa [U64] using x.isLt

theorem ofNat64_toNat_of_lt {value : Nat} (hvalue : value < U64) :
    (BitVec.ofNat 64 value).toNat = value := by
  rw [BitVec.toNat_ofNat]
  apply Nat.mod_eq_of_lt
  norm_num [U64] at hvalue ⊢
  exact hvalue

theorem src52_eq_of_u52 (x : QWord) (hx : x.toNat < U52) :
    src52 x = x.toNat := by
  exact Nat.mod_eq_of_lt hx

theorem qwordAdd_toNat_of_noWrap (x y : QWord)
    (h : x.toNat + y.toNat < U64) :
    (qwordAdd x y).toNat = x.toNat + y.toNat := by
  exact ofNat64_toNat_of_lt h

theorem qwordMul_toNat_of_noWrap (x y : QWord)
    (h : x.toNat * y.toNat < U64) :
    (qwordMul x y).toNat = x.toNat * y.toNat := by
  exact ofNat64_toNat_of_lt h

theorem qwordShiftLeft_toNat_of_noWrap (x : QWord) (amount : Nat)
    (h : x.toNat * 2 ^ amount < U64) :
    (qwordShiftLeft x amount).toNat = x.toNat * 2 ^ amount := by
  exact ofNat64_toNat_of_lt h

theorem qwordShiftRight_toNat (x : QWord) (amount : Nat) :
    (qwordShiftRight x amount).toNat = x.toNat / 2 ^ amount := by
  apply ofNat64_toNat_of_lt
  exact lt_of_le_of_lt (Nat.div_le_self _ _) (qword_toNat_lt x)

theorem qwordMask51_toNat (x : QWord) :
    (qwordMask51 x).toNat = x.toNat % B51 := by
  apply ofNat64_toNat_of_lt
  have hmod : x.toNat % B51 < B51 := Nat.mod_lt _ (by norm_num [B51])
  exact lt_trans hmod (by norm_num [B51, U64])

theorem vpmadd52luqLane_toNat_of_noWrap (acc x y : QWord)
    (h : acc.toNat + ifmaLo52 x y < U64) :
    (vpmadd52luqLane acc x y).toNat = acc.toNat + ifmaLo52 x y := by
  exact ofNat64_toNat_of_lt h

theorem vpmadd52huqLane_toNat_of_noWrap (acc x y : QWord)
    (h : acc.toNat + ifmaHi52 x y < U64) :
    (vpmadd52huqLane acc x y).toNat = acc.toNat + ifmaHi52 x y := by
  exact ofNat64_toNat_of_lt h

theorem ifmaLo52_eq_of_u52 (x y : QWord)
    (hx : x.toNat < U52) (hy : y.toNat < U52) :
    ifmaLo52 x y = (x.toNat * y.toNat) % U52 := by
  simp [ifmaLo52, src52_eq_of_u52 x hx, src52_eq_of_u52 y hy]

theorem ifmaHi52_eq_of_u52 (x y : QWord)
    (hx : x.toNat < U52) (hy : y.toNat < U52) :
    ifmaHi52 x y = (x.toNat * y.toNat) / U52 := by
  simp [ifmaHi52, src52_eq_of_u52 x hx, src52_eq_of_u52 y hy]

theorem vpmadd52luq_lane_independent (acc x y : Zmm) (lane : Fin 8) :
    vpmadd52luq acc x y lane = vpmadd52luqLane (acc lane) (x lane) (y lane) := by
  rfl

theorem vpmadd52huq_lane_independent (acc x y : Zmm) (lane : Fin 8) :
    vpmadd52huq acc x y lane = vpmadd52huqLane (acc lane) (x lane) (y lane) := by
  rfl

theorem vpaddq_lane_independent (x y : Zmm) (lane : Fin 8) :
    vpaddq x y lane = qwordAdd (x lane) (y lane) := by
  rfl

theorem vpmullq_lane_independent (x y : Zmm) (lane : Fin 8) :
    vpmullq x y lane = qwordMul (x lane) (y lane) := by
  rfl

end NaryaFormal.X86
