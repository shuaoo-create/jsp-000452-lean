import RegionComponentLayerBudget
import PortedComponentAlternatives
import GoodSplitLayerCost
import GoodFullAllocation
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
def largeGoodPieces (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (T : Set (G.induce Sᶜ).ConnectedComponent) : Set (G.induce Sᶜ).ConnectedComponent :=
  {c ∈ T | D<Nat.card c.supp}

theorem large_good_piece_split (G : SimpleGraph X) (S : Set X) (D : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (noReg : NoOriginalRegularCritical G D)
    (crit : ∀c : (G.induce Sᶜ).ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (inside : T⊆goodFullClass G S D)
    (c : (G.induce Sᶜ).ConnectedComponent) (large : c∈largeGoodPieces G S D T) :
    GoodPortSplit c.toSimpleGraph D := by
  obtain ⟨full,good⟩ := inside large.1
  rcases ported_component_alternatives G S D cap noReg c full (crit c) good with small|split
  · exact False.elim (Nat.not_lt_of_ge small.2.2 large.2)
  · exact split

theorem good_region_layer_cost (G : SimpleGraph X) (S : Set X) (D : ℕ) (hD : 2≤D)
    (even : Even D) (cap : ∀x,Nat.card (G.neighborSet x)≤D) (noReg : NoOriginalRegularCritical G D)
    (data : ∀c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (inside : T⊆goodFullClass G S D) :
    deletionBudget (G.induce (regionCore G S T)) (D-1) ≤ (largeGoodPieces G S D T).ncard := by
  classical
  let _ := Fintype.ofFinite T
  let B := largeGoodPieces G S D T
  have bound (c : T) : deletionBudget c.val.toSimpleGraph (D-1) ≤ if D<Nat.card c.val.supp then 1 else 0 := by
    by_cases big : D<Nat.card c.val.supp
    · rw [if_pos big]
      have split := large_good_piece_split G S D cap noReg (fun x => (data x).2) T inside c.val ⟨c.property,big⟩
      apply good_split_penultimate_cost _ D hD _ (data c.val).2 (inside c.property).2 split
      intro x
      exact (induced_neighbor_count_le _ _ x).trans ((induced_neighbor_count_le _ _ x.val).trans (cap _))
    · rw [if_neg big,odd_order_layer_zero _ D hD even (data c.val).1 (by omega)]
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => bound c)
  rw [Finset.sum_boole] at total
  let f : Finset T := Finset.univ.filter (fun c => D<Nat.card c.val.supp)
  have image : Subtype.val '' (↑f : Set ↥T)=B := by
    ext c
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨x.property,(Finset.mem_filter.mp hx).2⟩
    · intro hc
      exact ⟨⟨c,hc.1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hc.2⟩,rfl⟩
  have num := Set.ncard_image_of_injective (↑f : Set ↥T) Subtype.val_injective
  rw [image,Set.ncard_coe_finset] at num
  rw [region_component_layer_budget]
  exact total.trans_eq num.symm
#print axioms good_region_layer_cost
end JSP452Audit.StarHost
