import ActualNinePortErasureCost
import WholeComponentSubsetSumMenu
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem subfamily_rank_le_sum {I X : Type*} [DecidableEq I] [Finite X]
    (part : I→SimpleGraph X) (T : Finset I) :
    matchingEdges (T.sup part)≤∑i∈T,matchingEdges (part i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [matchingEdges_bot]
  | @insert i T fresh ih =>
    rw [Finset.sup_insert,Finset.sum_insert fresh]
    exact (rank_of_two_edge_colours _ (part i) (T.sup part) le_rfl).trans (Nat.add_le_add_left ih _)

namespace NinePortRegion
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem finite_adapted_union : Finset.univ.sup R.portPart=R.adapted := by
  have two : (Finset.univ:Finset (Fin 2))={0,1} := by decide
  rw [two];simp only [Finset.sup_insert,Finset.sup_singleton]

theorem actual_adapted_menu_row {s t r : ℕ} (n m : ℕ→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i<s,0<n i) (pm : ∀j<t,0<m j) (row : ForcingRow G s t n m r) (U : Set X)
    (menu : SplitCapacities R.capacity (r+U.ncard)) :
    ForcingRow (R.erased.induce Uᶜ) s t n m (r+U.ncard+R.totalCapacity) := by
  have cost (T : Finset (Fin 2)) : matchingEdges (T.sup R.portPart)≤∑i∈T,R.capacity i := by
    simpa only [R.portPart_rank] using subfamily_rank_le_sum R.portPart T
  have h := actual_piece_menu_of_splits G U R.portPart R.capacity n m hn hm pn pm
    (fun _ _ _ edge => edge.1) cost menu row
  rwa [R.finite_adapted_union,Fin.sum_univ_two] at h

end NinePortRegion

/-- Every admissible paid menu loses at least 9+e-h units relative to
deleting |U| nine-degree vertices on this same edge-erased graph. -/
theorem strict_nine_adapted_menu_price (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (U : Set F.X)
    (menu : SplitCapacities R.capacity (F.r+U.ncard)) :
    R.erased.edgeSet.ncard+9+R.portCount ≤
      (R.erased.induce Uᶜ).edgeSet.ncard+9*U.ncard+highestWidth F.n F.m F.r := by
  let P := R.totalCapacity
  let q := U.ncard+P
  let Y := R.erased.induce Uᶜ
  have row := R.actual_adapted_menu_row _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row U menu
  have actual : ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+q) := by
    simpa [q,P,Y,Nat.add_assoc] using row
  have large := (R.inner 0).2
  change 5≤R.capacity 0 at large
  have positive : 0<q := by change 0<U.ncard+(R.capacity 0+R.capacity 1);omega
  have small : rowCount F.s F.t (F.r+q)<F.rank := by
    have live := F.live;dsimp [StrictFamily.rank,rowCount] at live ⊢;omega
  have pay := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+q) actual small
  have feeUpper := prefix_column_tax F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r q F.live
  rw [nine] at feeUpper
  have cap (x : F.X) : Nat.card (F.G.neighborSet x)≤9 := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have fee := (R.adapted_edge_account cap).2.2
  change F.G.edgeSet.ncard=R.erased.edgeSet.ncard+9*P+8+R.portCount at fee
  have strict := F.strict
  change R.erased.edgeSet.ncard+9+R.portCount≤Y.edgeSet.ncard+9*U.ncard+highestWidth F.n F.m F.r
  dsimp only [q] at feeUpper pay
  omega

#print axioms subfamily_rank_le_sum
#print axioms NinePortRegion.finite_adapted_union
#print axioms NinePortRegion.actual_adapted_menu_row
#print axioms strict_nine_adapted_menu_price
end JSP452Audit.StarHost
