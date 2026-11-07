import PathCycleSplit
import DegreeTwoComponents
import BudgetCeiling

namespace JSP452Audit.StarHost
open SimpleGraph

theorem CanSplitRank.of_iso {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (e : G ≃g H) (split : CanSplitRank G) :
    CanSplitRank H := by
  intro u hu
  have ranks := rank_eq_of_graph_iso e
  obtain ⟨R,sub,red,blue⟩ := split u (hu.trans_eq ranks.symm)
  let K := R.comap e.symm
  refine ⟨K,?_,?_,?_⟩
  · intro x y h
    exact e.symm.map_rel_iff.mp (sub h)
  · exact (rank_eq_of_graph_iso (SimpleGraph.Iso.comap e.symm.toEquiv R)).le.trans red
  · have eq : H \ K = (G \ R).comap e.symm := by
      ext x y
      change (H.Adj x y ∧ ¬R.Adj (e.symm x) (e.symm y)) ↔
        (G.Adj (e.symm x) (e.symm y) ∧ ¬R.Adj (e.symm x) (e.symm y))
      rw [e.symm.map_rel_iff]
    rw [eq,← ranks]
    exact (rank_eq_of_graph_iso (SimpleGraph.Iso.comap e.symm.toEquiv (G \ R))).le.trans blue

theorem canSplitRank_iso_iff {X Y : Type*} [Finite X] [Finite Y] {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : G ≃g H) : CanSplitRank G ↔ CanSplitRank H :=
  ⟨CanSplitRank.of_iso e,CanSplitRank.of_iso e.symm⟩

private theorem sum_colors {X Y : Type*} {G A : SimpleGraph X} {H B : SimpleGraph Y}
    (a : A ≤ G) (b : B ≤ H) :
    A ⊕g B ≤ G ⊕g H ∧ (G ⊕g H) \ (A ⊕g B) = (G \ A) ⊕g (H \ B) := by
  constructor
  · rintro (x|x) (y|y) h
    · exact a h
    · exact (not_adj_sum_inl_inr _ _ h).elim
    · exact (not_adj_sum_inl_inr _ _ h.symm).elim
    · exact b h
  · ext x y
    rcases x with x|x <;> rcases y with y|y <;> simp

/-- Only one side of the disjoint sum needs a partial split; the other side
is monochromatic, so the additive allowance is used at most once. -/
theorem CanSplitRank.sumGraph {X Y : Type*} [Finite X] [Finite Y]
    {G : SimpleGraph X} {H : SimpleGraph Y} (left : CanSplitRank G) (right : CanSplitRank H) :
    CanSplitRank (G ⊕g H) := by
  intro u hu
  rw [matchingEdges_sumGraph] at hu
  by_cases takeLeft : u ≤ matchingEdges G
  · obtain ⟨A,hA,r,b⟩ := left u takeLeft
    obtain ⟨sub,complement⟩ := sum_colors hA (bot_le : (⊥ : SimpleGraph Y) ≤ H)
    refine ⟨_,sub,?_,?_⟩
    · simpa only [matchingEdges_sumGraph,matchingEdges_bot,Nat.add_zero] using r
    · rw [complement,sdiff_bot,matchingEdges_sumGraph,matchingEdges_sumGraph]
      omega
  · have room : u - matchingEdges G ≤ matchingEdges H := by omega
    obtain ⟨B,hB,r,b⟩ := right _ room
    obtain ⟨sub,complement⟩ := sum_colors (le_refl G) hB
    refine ⟨_,sub,?_,?_⟩
    · rw [matchingEdges_sumGraph]
      omega
    · rw [complement,sdiff_self,matchingEdges_sumGraph,matchingEdges_bot,Nat.zero_add,matchingEdges_sumGraph]
      omega

private def componentUnion {X : Type*} (G : SimpleGraph X) (T : Finset G.ConnectedComponent) : Set X :=
  {v | G.connectedComponentMk v ∈ T}

/-- Assemble the actual finite components; this also covers the empty graph. -/
theorem CanSplitRank.of_components {X : Type*} [Finite X] (G : SimpleGraph X)
    (parts : ∀ c : G.ConnectedComponent, CanSplitRank c.toSimpleGraph) : CanSplitRank G := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  have unionSplit (T : Finset G.ConnectedComponent) : CanSplitRank (G.induce (componentUnion G T)) := by
    induction T using Finset.induction_on with
    | empty =>
      have eq : G.induce (componentUnion G ∅) = ⊥ := by
        ext x
        exact (Finset.notMem_empty _ x.property).elim
      rw [eq]
      intro u hu
      refine ⟨⊥,le_rfl,?_,?_⟩ <;> simp [matchingEdges_bot]
    | @insert c T fresh ih =>
      have cover : c.supp ∪ componentUnion G T = componentUnion G (insert c T) := by
        ext x; exact Finset.mem_insert.symm
      have apart : Disjoint c.supp (componentUnion G T) := Set.disjoint_left.mpr (by
        intro x hx ht
        exact fresh ((show G.connectedComponentMk x = c from hx) ▸ ht))
      have sep : ∀ x∈c.supp, ∀ y∈componentUnion G T, ¬G.Adj x y :=
        fun _ hx _ hy edge => Set.disjoint_left.mp apart ((c.mem_supp_congr_adj edge).mp hx) hy
      exact CanSplitRank.of_iso (regionSumIso G _ _ _ cover apart sep) ((parts c).sumGraph ih)
  have all : componentUnion G Finset.univ = Set.univ := by ext; simp [componentUnion]
  have result := unionSplit Finset.univ
  rw [all] at result
  exact CanSplitRank.of_iso (induceUnivIso G) result

/-- The global reduction uses the true order of each classified connected component. -/
theorem degree_two_split_of_path_cycle
    (paths : ∀ n, CanSplitRank (pathGraph n)) (cycles : ∀ n, 3 ≤ n → CanSplitRank (cycleGraph n))
    {X : Type*} [Finite X] (G : SimpleGraph X) (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) :
    CanSplitRank G := by
  apply CanSplitRank.of_components
  intro c
  rcases degree_two_component_classification G cap c with path | cycle
  · obtain ⟨e⟩ := path
    exact CanSplitRank.of_iso e (paths _)
  · obtain ⟨large,⟨e⟩⟩ := cycle
    exact CanSplitRank.of_iso e (cycles _ large)

/-- A global coloring theorem for every finite graph of maximum degree at most two. -/
theorem canSplitRank_of_degree_le_two {X : Type*} [Finite X] (G : SimpleGraph X)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ 2) : CanSplitRank G :=
  degree_two_split_of_path_cycle canSplitRank_pathGraph (fun n _ => canSplitRank_cycleGraph n) G cap

#print axioms canSplitRank_of_degree_le_two
#print axioms CanSplitRank.of_iso
#print axioms CanSplitRank.sumGraph
#print axioms CanSplitRank.of_components
#print axioms degree_two_split_of_path_cycle
end JSP452Audit.StarHost
