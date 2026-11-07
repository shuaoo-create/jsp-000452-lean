import OriginalMissingHeightWitness
import ThreeStarBarrier
namespace JSP452Audit.StarHost
open SimpleGraph

/-- The full forest versus any positive q-component opponent supplies
the strong endpoint bound on an actual tight barrier with critical pieces. -/
theorem full_forest_endpoint {X : Type*} [Finite X] (G : SimpleGraph X)
    {s q : ℕ} (hs : 0<s) (hq : 0<q) (n : Fin s→ℕ) (m : Fin q→ℕ)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (force : Forces G (forest n) (forest m))
    (S : Set X) (tight : IsTightBarrier G S)
    (crit : ∀c:(G.induce Sᶜ).ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph)
    (d : ℕ) (pos : 0<d) (balance : matchingEdges G+d=s+q-1) :
    S.ncard+2*(d+∑i,(n i-1)/2)≤q := by
  let H := G.induce Sᶜ
  have rank := tight_deletes_rank G S S tight Set.Subset.rfl
  change matchingEdges G=S.ncard+matchingEdges H at rank
  have empty := tight_deletes_rank G S ∅ tight (Set.empty_subset _)
  rw [Set.ncard_empty,Nat.zero_add] at empty
  have red := forced_blue_off_short_cover G m n pm pn (forces_swap force) ∅ (by simpa using hq)
  have blue := forced_blue_off_short_cover G n m pn pm force ∅ (by simpa using hs)
  have redRank := forest_copy_matching _ n pn red
  have blueRank := forest_copy_matching _ m pm blue
  rw [Fintype.card_fin,←empty] at redRank blueRank
  have small := forcing_tight_barrier_size G m n pm pn (forces_swap force) (by omega) S tight
  have robust (U : Set ↥(Sᶜ : Set X)) (budget : U.ncard≤matchingEdges H+d-s) :
      (forest n).IsContained (H.induce Uᶜ) := by
    have count := outerCut_ncard S U
    have short : (outerCut S U).ncard<q := by omega
    obtain ⟨f⟩ := forced_blue_off_short_cover G m n pm pn (forces_swap force) (outerCut S U) short
    exact ⟨(nestedCutIso G S U).symm.toCopy.comp f⟩
  have price := robust_whole_half_order H n pn crit d (by omega) (by omega) robust
  omega

/-- For a complete row with positive matching deficit, apply the two
monochrome endpoints to the same tight barrier and original star lists. -/
theorem full_row_endpoint_guards {X : Type*} [Finite X] (G : SimpleGraph X)
    {s t r : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (S : Set X) (tight : IsTightBarrier G S)
    (crit : ∀c:(G.induce Sᶜ).ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph)
    (d : ℕ) (pos : 0<d) (balance : matchingEdges G+d=rowCount s t r) :
    S.ncard+r+2*(d+∑i,(n i-1)/2)≤t ∧ S.ncard+r+2*(d+∑j,(m j-1)/2)≤s := by
  have zero : matchingEdges (⊥:SimpleGraph X)+matchingEdges (G \ ⊥)+d=rowCount s t r := by
    simpa only [matchingEdges_bot,sdiff_bot,Nat.zero_add] using balance
  have small : matchingEdges (⊥:SimpleGraph X)<min s t := by rw [matchingEdges_bot];omega
  have guard := (forcing_row_strong_lengths_of_coloring G hs ht _ _ (pad_positive n pn) (pad_positive m pm)
    row ⊥ bot_le d pos zero small).1
  rw [matchingEdges_bot,Nat.zero_add] at guard
  have endR := row 0 r s (t-r) (by omega) (by omega) (by omega) hs (by omega)
  have endB := row r 0 (s-r) t (by omega) (by omega) (by omega) (by omega) ht
  let nr (z:Fin (s-r)) := padDemand n (r+z.val)
  let mr (z:Fin (t-r)) := padDemand m (r+z.val)
  have origN : (fun z:Fin s => padDemand n (0+z.val))=n := by funext z;simp [padDemand,z.isLt]
  have origM : (fun z:Fin t => padDemand m (0+z.val))=m := by funext z;simp [padDemand,z.isLt]
  change Forces G (forest (fun z:Fin s => padDemand n (0+z.val))) (forest mr) at endR
  change Forces G (forest nr) (forest (fun z:Fin t => padDemand m (0+z.val))) at endB
  rw [origN] at endR;rw [origM] at endB
  have red := full_forest_endpoint G hs (by omega : 0<t-r) n mr pn
    (fun z => pad_positive m pm _ (by have := z.isLt;omega)) endR S tight crit d pos
    (by dsimp [rowCount] at balance;omega)
  have blue := full_forest_endpoint G ht (by omega : 0<s-r) m nr pm
    (fun z => pad_positive n pn _ (by have := z.isLt;omega)) (forces_swap endB) S tight crit d pos
    (by dsimp [rowCount] at balance;omega)
  omega

#print axioms full_forest_endpoint
#print axioms full_row_endpoint_guards
end JSP452Audit.StarHost
