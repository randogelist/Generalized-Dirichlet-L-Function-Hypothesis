import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Exp

set_option autoImplicit false

noncomputable section

namespace HVRCyclotomicPacketTower

abbrev Packet := Nat → Nat → ℂ

def variation (F : Packet) (d : Nat) : ℝ :=
  Finset.sum (Finset.range (d + 1)) (fun j => ‖F d j‖)

def Subexponential (V : Nat → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ C : ℝ, 0 < C ∧
      ∀ d : Nat,
        V d ≤ C * Real.exp (ε * (d : ℝ))

def PacketSubexp (F : Packet) : Prop :=
  Subexponential (variation F)

theorem subexponential_of_le
    {V W : Nat → ℝ}
    (hVW : ∀ d : Nat, V d ≤ W d)
    (hW : Subexponential W) :
    Subexponential V := by
  intro ε hε
  obtain ⟨C, hC, hbound⟩ := hW ε hε
  refine ⟨C, hC, ?_⟩
  intro d
  exact le_trans (hVW d) (hbound d)

theorem subexponential_zero :
    Subexponential (fun _ : Nat => 0) := by
  intro ε hε
  refine ⟨1, zero_lt_one, ?_⟩
  intro d
  have h : 0 ≤ Real.exp (ε * (d : ℝ)) := (Real.exp_pos _).le
  simpa using h

theorem subexponential_add
    {V W : Nat → ℝ}
    (hV : Subexponential V)
    (hW : Subexponential W) :
    Subexponential (fun d => V d + W d) := by
  intro ε hε
  obtain ⟨CV, hCV, hVb⟩ := hV ε hε
  obtain ⟨CW, hCW, hWb⟩ := hW ε hε
  refine ⟨CV + CW, add_pos hCV hCW, ?_⟩
  intro d
  calc
    V d + W d
        ≤ CV * Real.exp (ε * (d : ℝ)) +
            CW * Real.exp (ε * (d : ℝ)) :=
      add_le_add (hVb d) (hWb d)
    _ = (CV + CW) * Real.exp (ε * (d : ℝ)) := by
      ring

theorem variation_add_le
    (F G : Packet) (d : Nat) :
    variation (F + G) d ≤ variation F d + variation G d := by
  unfold variation
  calc
    Finset.sum (Finset.range (d + 1))
        (fun j => ‖(F + G) d j‖)
      ≤
    Finset.sum (Finset.range (d + 1))
        (fun j => ‖F d j‖ + ‖G d j‖) := by
      apply Finset.sum_le_sum
      intro j hj
      simpa using norm_add_le (F d j) (G d j)
    _ =
      Finset.sum (Finset.range (d + 1)) (fun j => ‖F d j‖) +
      Finset.sum (Finset.range (d + 1)) (fun j => ‖G d j‖) := by
      rw [Finset.sum_add_distrib]

theorem variation_neg
    (F : Packet) (d : Nat) :
    variation (-F) d = variation F d := by
  unfold variation
  apply Finset.sum_congr rfl
  intro j hj
  simp

theorem packetSubexp_zero :
    PacketSubexp (0 : Packet) := by
  unfold PacketSubexp
  apply subexponential_of_le (W := fun _ : Nat => 0)
  · intro d
    simp [variation]
  · exact subexponential_zero

theorem packetSubexp_add
    {F G : Packet}
    (hF : PacketSubexp F)
    (hG : PacketSubexp G) :
    PacketSubexp (F + G) := by
  unfold PacketSubexp at hF hG ⊢
  apply subexponential_of_le (variation_add_le F G)
  exact subexponential_add hF hG

theorem packetSubexp_neg
    {F : Packet}
    (hF : PacketSubexp F) :
    PacketSubexp (-F) := by
  unfold PacketSubexp at hF ⊢
  have hvar : variation (-F) = variation F := by
    funext d
    exact variation_neg F d
  rw [hvar]
  exact hF

theorem packetSubexp_sub
    {F G : Packet}
    (hF : PacketSubexp F)
    (hG : PacketSubexp G) :
    PacketSubexp (F - G) := by
  have h : PacketSubexp (F + (-G)) :=
    packetSubexp_add hF (packetSubexp_neg hG)
  simpa [sub_eq_add_neg] using h

theorem packetSubexp_finset_sum
    {ι : Type*}
    (s : Finset ι)
    (F : ι → Packet)
    (hF : ∀ i ∈ s, PacketSubexp (F i)) :
    PacketSubexp (Finset.sum s F) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using packetSubexp_zero
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      apply packetSubexp_add
      · exact hF a (by simp)
      · apply ih
        intro i hi
        exact hF i (by simp [hi])

theorem packetSubexp_moebius_smul
    (n : Nat)
    {F : Packet}
    (hF : PacketSubexp F) :
    PacketSubexp ((ArithmeticFunction.moebius n) • F) := by
  rcases ArithmeticFunction.moebius_eq_or n with h0 | h1 | hneg
  · rw [h0]
    simpa using packetSubexp_zero
  · rw [h1]
    simpa using hF
  · rw [hneg]
    simpa using packetSubexp_neg hF

def DivisorDecomposition
    (cyclo prim : Nat → Packet) : Prop :=
  ∀ q : Nat, 0 < q →
    Finset.sum q.divisors prim = cyclo q

theorem exactConductorRecovery
    (cyclo prim : Nat → Packet)
    (hdecomp : DivisorDecomposition cyclo prim) :
    ∀ q : Nat, 0 < q →
      Finset.sum q.divisorsAntidiagonal
        (fun x =>
          (ArithmeticFunction.moebius x.1) • cyclo x.2) =
        prim q := by
  exact
    (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq).mp
      hdecomp

theorem primitiveSubexp_of_cyclotomicSubexp
    (cyclo prim : Nat → Packet)
    (hdecomp : DivisorDecomposition cyclo prim)
    (hCyclo : ∀ q : Nat, 0 < q → PacketSubexp (cyclo q)) :
    ∀ q : Nat, 0 < q → PacketSubexp (prim q) := by
  intro q hq
  have hrecover :
      Finset.sum q.divisorsAntidiagonal
        (fun x =>
          (ArithmeticFunction.moebius x.1) • cyclo x.2) =
        prim q :=
    exactConductorRecovery cyclo prim hdecomp q hq
  rw [← hrecover]
  apply packetSubexp_finset_sum
  intro x hx
  apply packetSubexp_moebius_smul
  have hsnd :
      x.2 ∈ q.divisors :=
    Nat.snd_mem_divisors_of_mem_antidiagonal hx
  exact hCyclo x.2 (Nat.pos_of_mem_divisors hsnd)

theorem cyclotomicSubexp_of_primitiveSubexp
    (cyclo prim : Nat → Packet)
    (hdecomp : DivisorDecomposition cyclo prim)
    (hPrim : ∀ q : Nat, 0 < q → PacketSubexp (prim q)) :
    ∀ q : Nat, 0 < q → PacketSubexp (cyclo q) := by
  intro q hq
  have hsum :
      Finset.sum q.divisors prim = cyclo q :=
    hdecomp q hq
  rw [← hsum]
  apply packetSubexp_finset_sum
  intro f hf
  exact hPrim f (Nat.pos_of_mem_divisors hf)

theorem GLOBAL_CYCLOTOMIC_PRIMITIVE_HVR_EQUIVALENCE
    (cyclo prim : Nat → Packet)
    (hdecomp : DivisorDecomposition cyclo prim) :
    (∀ q : Nat, 0 < q → PacketSubexp (cyclo q)) ↔
      (∀ q : Nat, 0 < q → PacketSubexp (prim q)) := by
  constructor
  · exact primitiveSubexp_of_cyclotomicSubexp cyclo prim hdecomp
  · exact cyclotomicSubexp_of_primitiveSubexp cyclo prim hdecomp

def relativePacket
    (cyclo : Nat → Packet)
    (m q : Nat) : Packet :=
  cyclo m - cyclo q

theorem RELATIVE_PACKET_STEP_EQUIVALENCE
    (cyclo : Nat → Packet)
    {m q : Nat}
    (hDq : PacketSubexp (cyclo q)) :
    PacketSubexp (cyclo m) ↔
      PacketSubexp (relativePacket cyclo m q) := by
  constructor
  · intro hDm
    exact packetSubexp_sub hDm hDq
  · intro hRel
    have hsum :
        PacketSubexp (relativePacket cyclo m q + cyclo q) :=
      packetSubexp_add hRel hDq
    have heq :
        relativePacket cyclo m q + cyclo q = cyclo m := by
      funext d j
      simp [relativePacket]
    rw [heq] at hsum
    exact hsum

theorem RELATIVE_PACKET_STEP_EQUIVALENCE_OF_DVD
    (cyclo : Nat → Packet)
    {m q : Nat}
    (_hqm : q ∣ m)
    (hDq : PacketSubexp (cyclo q)) :
    PacketSubexp (cyclo m) ↔
      PacketSubexp (relativePacket cyclo m q) :=
  RELATIVE_PACKET_STEP_EQUIVALENCE cyclo hDq

theorem propagateAlongRelativeChain
    (cyclo : Nat → Packet)
    (level : Nat → Nat)
    (hBase : PacketSubexp (cyclo (level 0)))
    (hRel :
      ∀ i : Nat,
        PacketSubexp
          (relativePacket cyclo (level (i + 1)) (level i))) :
    ∀ r : Nat, PacketSubexp (cyclo (level r)) := by
  intro r
  induction r with
  | zero =>
      simpa using hBase
  | succ r ih =>
      exact
        (RELATIVE_PACKET_STEP_EQUIVALENCE cyclo ih).mpr
          (hRel r)

theorem RH_IMPLIES_GRH_OF_CYCLOTOMIC_PACKET_PROPAGATION
    (cyclo prim : Nat → Packet)
    (hdecomp : DivisorDecomposition cyclo prim)
    (RH GRH : Prop)
    (hRHBase :
      RH → PacketSubexp (cyclo 1))
    (hPropagate :
      PacketSubexp (cyclo 1) →
        ∀ q : Nat, 0 < q → PacketSubexp (cyclo q))
    (hPrimitiveToGRH :
      (∀ q : Nat, 0 < q → PacketSubexp (prim q)) →
        GRH) :
    RH → GRH := by
  intro hRH
  have hCyclo :
      ∀ q : Nat, 0 < q → PacketSubexp (cyclo q) :=
    hPropagate (hRHBase hRH)
  have hPrim :
      ∀ q : Nat, 0 < q → PacketSubexp (prim q) :=
    (GLOBAL_CYCLOTOMIC_PRIMITIVE_HVR_EQUIVALENCE
      cyclo prim hdecomp).mp hCyclo
  exact hPrimitiveToGRH hPrim

theorem HVR_CYCLOTOMIC_COMPLETED_PACKET_TOWER
    (cyclo prim : Nat → Packet)
    (hdecomp : DivisorDecomposition cyclo prim) :
    ((∀ q : Nat, 0 < q → PacketSubexp (cyclo q)) ↔
      (∀ q : Nat, 0 < q → PacketSubexp (prim q))) ∧
    (∀ m q : Nat,
      PacketSubexp (cyclo q) →
        (PacketSubexp (cyclo m) ↔
          PacketSubexp (relativePacket cyclo m q))) := by
  constructor
  · exact GLOBAL_CYCLOTOMIC_PRIMITIVE_HVR_EQUIVALENCE
      cyclo prim hdecomp
  · intro m q hq
    exact RELATIVE_PACKET_STEP_EQUIVALENCE cyclo hq

end HVRCyclotomicPacketTower

#check HVRCyclotomicPacketTower.Subexponential
#check HVRCyclotomicPacketTower.PacketSubexp
#check HVRCyclotomicPacketTower.DivisorDecomposition
#check HVRCyclotomicPacketTower.exactConductorRecovery
#check HVRCyclotomicPacketTower.GLOBAL_CYCLOTOMIC_PRIMITIVE_HVR_EQUIVALENCE
#check HVRCyclotomicPacketTower.RELATIVE_PACKET_STEP_EQUIVALENCE
#check HVRCyclotomicPacketTower.propagateAlongRelativeChain
#check HVRCyclotomicPacketTower.RH_IMPLIES_GRH_OF_CYCLOTOMIC_PACKET_PROPAGATION
#check HVRCyclotomicPacketTower.HVR_CYCLOTOMIC_COMPLETED_PACKET_TOWER

#print axioms HVRCyclotomicPacketTower.exactConductorRecovery
#print axioms HVRCyclotomicPacketTower.GLOBAL_CYCLOTOMIC_PRIMITIVE_HVR_EQUIVALENCE
#print axioms HVRCyclotomicPacketTower.RELATIVE_PACKET_STEP_EQUIVALENCE
#print axioms HVRCyclotomicPacketTower.propagateAlongRelativeChain
#print axioms HVRCyclotomicPacketTower.RH_IMPLIES_GRH_OF_CYCLOTOMIC_PACKET_PROPAGATION
#print axioms HVRCyclotomicPacketTower.HVR_CYCLOTOMIC_COMPLETED_PACKET_TOWER
