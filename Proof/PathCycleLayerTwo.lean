import PathCycleMatching
import ZeroBudgetExposure
import BarrierExitCount
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

theorem deletionBudget_le_unmatched_count {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (pos : 0<D) (cap : ∀ v, Nat.card (G.neighborSet v)≤D) :
    deletionBudget G D ≤ minUnmatched G := by
  obtain ⟨M,hm,max⟩ := exists_maximum_matching G
  have small : exposedFull G M D ⊆ M.vertsᶜ := fun _ h => h.1
  have eq := maximum_uncovered_count M hm max
  exact (deletionBudget_le_minimumExposure G D pos cap).trans
    ((minimumExposure_le G D M hm max).trans ((Set.ncard_le_ncard small).trans_eq eq))

theorem cycle_budget_two_bound (n : ℕ) (hn : 3≤n) : deletionBudget (cycleGraph n) 2 ≤ n%2 := by
  have cap : ∀ x : Fin n, Nat.card ((cycleGraph n).neighborSet x) ≤ 2 := by
    obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm 3 m]
    intro x
    rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree,cycleGraph_degree_three_le]
  have h := deletionBudget_le_unmatched_count (cycleGraph n) 2 (by decide) cap
  rw [minUnmatched_eq_deficit,Nat.card_fin,cycleGraph_matchingEdges] at h
  omega

/-- On an indexed path, no full-degree point is missed by the alternating path matching.
The only possible unmatched vertex is the final endpoint of an odd path. -/
theorem path_budget_two_zero (n : ℕ) : deletionBudget (pathGraph n) 2=0 := by
  let G := pathGraph n
  let even : Fin (n/2) ↪ Fin n := {
    toFun i := ⟨2*i.val,by have := i.isLt; omega⟩
    inj' := fun _ _ h => Fin.ext (by have e := congrArg (fun j : Fin n => j.val) h; dsimp at e; omega) }
  let odd : Fin (n/2) ↪ Fin n := {
    toFun i := ⟨2*i.val+1,by have := i.isLt; omega⟩
    inj' := fun _ _ h => Fin.ext (by have e := congrArg (fun j : Fin n => j.val) h; dsimp at e; omega) }
  have edge (a) : G.Adj (even a) (odd a) := pathGraph_adj.mpr (Or.inl rfl)
  have apart : Disjoint (Set.range even) (Set.range odd) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨k,rfl⟩ ⟨j,eq⟩
    have raw := congrArg (fun k : Fin n => k.val) eq
    change 2*j.val+1=2*k.val at raw; omega
  let M := pairFamily G even odd edge
  have hm := pairFamily_isMatching G even odd edge apart
  have max : M.edgeSet.ncard=matchingEdges G := by
    have rank := matching_vertices_eq_twice_edges hm
    rw [pairFamily_verts,Set.ncard_union_eq apart,Set.ncard_range_of_injective even.injective,
      Set.ncard_range_of_injective odd.injective,Nat.card_fin] at rank
    rw [pathGraph_matchingEdges]; change n/2+n/2=2*M.edgeSet.ncard at rank; omega
  have bound (x : Fin n) : Nat.card (G.neighborSet x)≤2 := by
    let encode (y : G.neighborSet x) : Fin 2 := if y.val.val<x.val then 0 else 1
    have inj : Function.Injective encode := by
      intro a b e
      have ha := pathGraph_adj.mp a.property
      have hb := pathGraph_adj.mp b.property
      apply Subtype.ext; apply Fin.ext
      dsimp [encode] at e; split_ifs at e <;> omega
    simpa using Nat.card_le_card_of_injective encode inj
  apply (deletionBudget_zero_iff_minimumExposure_zero G 2 (by decide) bound).2
  have none : exposedFull G M 2=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have miss := hx.1
    change x∉Set.range even ∪ Set.range odd at miss
    have last : 2*(n/2)≤x.val := by
      by_contra! notLast
      let i : Fin (n/2) := ⟨x.val/2,by omega⟩
      by_cases e : x.val%2=0
      · exact miss (Or.inl ⟨i,Fin.ext (by change 2*(x.val/2)=x.val; omega)⟩)
      · exact miss (Or.inr ⟨i,Fin.ext (by change 2*(x.val/2)+1=x.val; omega)⟩)
    have few : (G.neighborSet x).ncard≤1 := (Set.ncard_le_one (G.neighborSet x).toFinite).mpr (by
      intro a ha b hb
      have h1 := pathGraph_adj.mp ha; have h2 := pathGraph_adj.mp hb
      have := a.isLt; have := b.isLt; have := x.isLt; apply Fin.ext; omega)
    have full : (G.neighborSet x).ncard=2 := hx.2
    omega
  have lo := minimumExposure_le G 2 M hm max
  rw [none,Set.ncard_empty] at lo
  omega
#print axioms path_budget_two_zero
#print axioms cycle_budget_two_bound
end JSP452Audit.StarHost