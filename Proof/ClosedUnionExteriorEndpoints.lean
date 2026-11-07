import ClosedFullUnionMatchingLengths
import TwoColorBudgetExterior
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
open private JSP452Audit.StarHost.one_sum_residual from TwoColorBudgetExterior
namespace JSP452Audit.StarHost
open SimpleGraph

theorem closed_union_sum_row {X : Type*} (G : SimpleGraph X) (U : Set X)
    (closed : ∀v∈U,∀w,G.Adj v w → w∈U) {s t r : ℕ} {n m : ℕ→ℕ}
    (row : ForcingRow G s t n m r) : ForcingRow (G.induce Uᶜ⊕g G.induce U) s t n m r := by
  let e := regionSumIso G Set.univ Uᶜ U (Set.compl_union_self _) disjoint_compl_left
    (fun x hx y hy edge => hx (closed y hy x edge.symm))
  exact forcingRow_of_iso (e.trans (induceUnivIso G)).symm row

theorem closed_union_palette_row {X : Type*} (G : SimpleGraph X) (U : Set X)
    (closed : ∀v∈U,∀w,G.Adj v w → w∈U) {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ)
    (P : SimpleGraph U) (sub : P≤G.induce U) (W : RemovalBudget s) (V : RemovalBudget t)
    (red : AdmitsInternal W n P) (blue : AdmitsInternal V m ((G.induce U) \ P))
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ForcingRow (G.induce Uᶜ) W.len V.len (padDemand (W.entries n)) (padDemand (V.entries m)) r := by
  have actual := closed_union_sum_row G U closed row
  intro i j l q ij il jq pl pq R less
  have nlen : W.len≤s := Nat.sub_le _ _
  have mlen : V.len≤t := Nat.sub_le _ _
  have lenR : i+(s-i)=s := by omega
  have lenB : j+(t-j)=t := by omega
  have orig := actual i j (s-i) (t-j) ij lenR lenB (by omega) (by omega)
  obtain ⟨both,comp⟩ := JSP452Audit.StarHost.sum_colors less sub
  rcases orig _ both with redCopy|blueCopy
  · exact Or.inl (JSP452Audit.StarHost.one_sum_residual R P n W lenR il red redCopy)
  · rw [comp] at blueCopy
    exact Or.inr (JSP452Audit.StarHost.one_sum_residual _ _ m V lenB jq blue blueCopy)

theorem closed_union_exterior_endpoint {X : Type*} [Finite X] (G : SimpleGraph X) (U : Set X)
    (closed : ∀v∈U,∀w,G.Adj v w → w∈U) {s t r : ℕ} (hs : 0<s) (legal : r<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (R : SimpleGraph ↥(Uᶜ : Set X)) (sub : R≤G.induce Uᶜ) :
    (forest n).IsContained R ∨ t-r-matchingEdges (G.induce U)≤matchingEdges ((G.induce Uᶜ) \ R) := by
  have actual := closed_union_sum_row G U closed row
  have orig := actual 0 r s (t-r) (by omega) (by omega) (by omega) hs (by omega)
  have bot : (⊥:SimpleGraph U)≤G.induce U := bot_le
  obtain ⟨both,comp⟩ := JSP452Audit.StarHost.sum_colors sub bot
  rcases orig _ both with first|second
  · left
    have eq : (fun i:Fin s => padDemand n (0+i.val))=n := by
      funext i; simp [padDemand,i.isLt]
    change (forest (fun i:Fin s => padDemand n (0+i.val))).IsContained _ at first
    rw [eq] at first
    exact copy_in_left_summand R _ (forest_has_neighbor n pn) first
  · right
    rw [comp,sdiff_bot] at second
    have rank := forest_copy_matching _ (fun j:Fin (t-r) => padDemand m (r+j.val))
      (fun j => pad_positive m pm _ (by have := j.isLt;omega)) second
    rw [Fintype.card_fin,matchingEdges_sumGraph] at rank
    omega

#print axioms closed_union_sum_row
#print axioms closed_union_palette_row
#print axioms closed_union_exterior_endpoint
end JSP452Audit.StarHost
