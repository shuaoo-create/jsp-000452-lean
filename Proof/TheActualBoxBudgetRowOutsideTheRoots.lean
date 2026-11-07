import TheRootRetainingNineDegreeJoinedRow
open private JSP452Audit.StarHost.one_sum_residual from TwoColorBudgetExterior
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem one_budget_on_sum_row {X Y : Type*} [Finite X] [Finite Y] (O : SimpleGraph X) (C : SimpleGraph Y)
    {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (pm : ∀j,1≤m j) (W : RemovalBudget s)
    (adm : AdmitsInternal W n C) (row : ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    ForcingRow O W.len t (padDemand (W.entries n)) (padDemand m) r := by
  intro i j l q ij il jq pl pq R less
  have fit : W.len≤s := Nat.sub_le _ _
  let old := s-i
  have len : i+old=s := by dsimp only [old];omega
  have orig := row i j old q ij len jq (by omega) pq
  obtain ⟨both,comp⟩ := JSP452Audit.StarHost.sum_colors less (le_rfl : C≤C)
  rcases orig _ both with first|second
  · exact Or.inl (JSP452Audit.StarHost.one_sum_residual R C n W len il adm first)
  · right
    rw [comp,sdiff_self] at second
    let short (z : Fin q) := padDemand m (j+z.val)
    exact copy_in_left_summand (O \ R) (forest short)
      (forest_has_neighbor short (fun z => pad_positive m pm _ (by have := z.isLt;omega))) second

theorem strict_nine_two_physical_rows (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) :
    let C := F.G.induce R.chosen
    let O := F.G.induce R.outside
    let Z := eraseInternal F.G R.chosen
    let P := R.totalCapacity
    let a := R.roots.ncard
    let W := componentBudget C F.n
    let V := componentBudget C F.m
    (ForcingRow O W.len F.t (padDemand (W.entries F.n)) (padDemand F.m) (F.r+a) ∧
      ForcingRow Z W.len F.t (padDemand (commonErasedDemand F.n W a P)) (padDemand F.m) F.r) ∧
    (ForcingRow O V.len F.s (padDemand (V.entries F.m)) (padDemand F.n) (F.r+a) ∧
      ForcingRow Z V.len F.s (padDemand (commonErasedDemand F.m V a P)) (padDemand F.n) F.r) := by
  intro C O Z P a W V
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  have rk := (R.region_rank_edges cap).1
  have row := (strict_nine_root_deleted_row F paid nine R).2.2.2
  have wn := component_budget_admits C F.n F.pn
  have vm := component_budget_admits C F.m F.pm
  have one := R.complete_erased_core_row F.G W F.n F.m F.hn F.pn wn F.row
  have two := R.complete_erased_core_row F.G V F.m F.n F.hm F.pm vm (swap_positive_forcing_row _ _ _ F.row)
  rw [rk] at one two
  exact ⟨⟨one_budget_on_sum_row O C F.n F.m F.pm W wn row,one⟩,
    ⟨one_budget_on_sum_row O C F.m F.n F.pn V vm (swap_positive_forcing_row _ _ _ row),two⟩⟩

#print axioms one_budget_on_sum_row
#print axioms strict_nine_two_physical_rows
end JSP452Audit.StarHost
