import TheWholeLowLastColumnForcesSingletonSourceDeficiency
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ScaledPortPlan.excess_has_distinct_positive_support {A:Type u} [Finite A] {G:SimpleGraph A} {D k c:ℕ}
    {K:DegreeRegion G D} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (degree:0<D) (rho:0<P.excess)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) :
    P.excess≤P.positives.ncard ∧ (D%2=1 → P.excess<P.positives.ncard) := by
  classical
  let _ := Fintype.ofFinite ↥P.positives
  let n := P.positives.ncard
  let m := D/2
  let val (Q:↥P.positives) := edgeSurplus Q.val.toSimpleGraph D
  have each (Q:↥P.positives) : val Q≤(m:ℤ) := by
    let _ : Nonempty Q.val.supp := Q.val.nonempty_supp.to_subtype
    have ht := (positive_core_caps Q.val.toSimpleGraph (K.critical Q.val).2 D
      (fun x => (induced_neighbor_count_le (G.induce K.barrierᶜ) Q.val.supp x).trans
        ((induced_neighbor_count_le G K.barrierᶜ x.val).trans (cap x.val.val))) Q.property.2).2.1
    change 2*val Q≤(D:ℤ) at ht
    dsimp only [m];omega
  have cnt : Fintype.card ↥P.positives=n := (Nat.card_eq_fintype_card (α:=↥P.positives)).symm
  have sum := core_surplus_eq_sum G K.barrier P.positives D
  change P.weight=∑Q,val Q at sum
  have bound : P.weight≤(m:ℤ)*n := by
    rw [sum]
    calc
      _ ≤ ∑_Q:↥P.positives,(m:ℤ) := Finset.sum_le_sum (fun Q _ => each Q)
      _ = _ := by simp [cnt,mul_comm]
  have all := (P.exact_weight_and_root_cost E cap 0).1
  have chosen := positivePieces_dominate G K.barrier P.wholeFamily D
  change edgeSurplus (G.induce P.cutCore) D≤P.weight at chosen
  have low : (D:ℤ)*P.excess≤2*P.weight := by omega
  have two : 2*(m:ℤ)≤D := by dsimp only [m];omega
  have tot := mul_le_mul_of_nonneg_right two (show (0:ℤ)≤n by positivity)
  have count : P.excess≤n := by
    by_contra! no
    have clash := mul_lt_mul_of_pos_left (show (n:ℤ)<P.excess by exact_mod_cast no) (show (0:ℤ)<D by exact_mod_cast degree)
    linarith only [clash,low,bound,tot]
  refine ⟨count,?_⟩
  intro odd
  have strict : 2*(m:ℤ)<D := by dsimp only [m];omega
  have npos : 0<(n:ℤ) := by omega
  have less := mul_lt_mul_of_pos_right strict npos
  change P.excess<n
  by_contra! no
  have eq : P.excess=n := by omega
  rw [eq] at low
  linarith only [less,low,bound]

#print axioms ScaledPortPlan.excess_has_distinct_positive_support
end JSP452Audit.StarHost