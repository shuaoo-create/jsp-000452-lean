import MatchedDeletion
import Mathlib.Combinatorics.SimpleGraph.Tutte

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*}

/-- Join G to the complete graph on d new vertices; the original labels are preserved. -/
def tutteJoin (G : SimpleGraph X) (d : ℕ) : SimpleGraph (X ⊕ Fin d) where
  Adj
    | .inl x, .inl y => G.Adj x y
    | .inr i, .inr j => i ≠ j
    | _, _ => True
  symm := ⟨by
    rintro (x | i) (y | j) h
    · exact h.symm
    · trivial
    · trivial
    · exact Ne.symm h⟩
  loopless := ⟨by rintro (x | i) h; exact G.irrefl h; exact h rfl⟩

@[simp] theorem tutteJoin_old_adj (G : SimpleGraph X) (d : ℕ) (x y : X) :
    (tutteJoin G d).Adj (.inl x) (.inl y) ↔ G.Adj x y := Iff.rfl

@[simp] theorem tutteJoin_dummy_adj (G : SimpleGraph X) (d : ℕ) (i j : Fin d) :
    (tutteJoin G d).Adj (.inr i) (.inr j) ↔ i ≠ j := Iff.rfl

@[simp] theorem tutteJoin_old_dummy_adj (G : SimpleGraph X) (d : ℕ) (x : X) (i : Fin d) :
    (tutteJoin G d).Adj (.inl x) (.inr i) := trivial

@[simp] theorem tutteJoin_dummy_old_adj (G : SimpleGraph X) (d : ℕ) (i : Fin d) (x : X) :
    (tutteJoin G d).Adj (.inr i) (.inl x) := trivial

/-- Retain exactly the original pairs that were matched to one another. -/
def tutteJoinRestrict {G : SimpleGraph X} {d : ℕ} (M : (tutteJoin G d).Subgraph) : G.Subgraph where
  verts := {x | ∃ y : X, M.Adj (.inl x) (.inl y)}
  Adj x y := M.Adj (.inl x) (.inl y)
  adj_sub := fun h => M.adj_sub h
  edge_vert := fun h => ⟨_, h⟩
  symm := ⟨fun _ _ h => h.symm⟩

theorem tutteJoinRestrict_isMatching {G : SimpleGraph X} {d : ℕ}
    {M : (tutteJoin G d).Subgraph} (hM : M.IsMatching) :
    (tutteJoinRestrict M).IsMatching := by
  rintro _ ⟨y,hy⟩
  exact ⟨y,hy,fun _ hz => Sum.inl.inj (hM.eq_of_adj_left hz hy)⟩

/-- Every old vertex lost by restriction has a different dummy as its partner. -/
theorem tutteJoinRestrict_missed_le {G : SimpleGraph X} {d : ℕ}
    {M : (tutteJoin G d).Subgraph} (perf : M.IsPerfectMatching) :
    Nat.card {v : X // v ∉ (tutteJoinRestrict M).verts} ≤ d := by
  classical
  let U := {v : X // v ∉ (tutteJoinRestrict M).verts}
  have mate (x : U) : ∃ i : Fin d, M.Adj (.inl x.val) (.inr i) := by
    obtain ⟨y,hy,_⟩ := SimpleGraph.Subgraph.isPerfectMatching_iff.mp perf (.inl x.val)
    rcases y with y | i
    · exact (x.property ⟨y,hy⟩).elim
    · exact ⟨i,hy⟩
  let f (x : U) := (mate x).choose
  have inj : Function.Injective f := by
    intro x y h
    have hy : M.Adj (.inl y.val) (.inr (f x)) := h ▸ (mate y).choose_spec
    exact Subtype.ext (Sum.inl.inj (perf.1.eq_of_adj_right (mate x).choose_spec hy))
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f inj

private theorem matching_count_aux {G : SimpleGraph X} {N : G.Subgraph}
    [Fintype N.verts] (h : N.IsMatching) :
    N.verts.ncard = 2 * N.coe.edgeSet.ncard := by
  classical
  have count : N.verts.toFinset.card = 2 * N.coe.edgeFinset.card := by
    rw [SimpleGraph.Subgraph.isMatching_iff_forall_degree] at h
    rw [← N.coe.sum_degrees_eq_twice_card_edges]
    simp [h, Finset.card_univ]
  rw [Set.ncard_eq_toFinset_card' N.verts, count, ← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]

theorem matching_vertices_eq_twice_edges [Finite X] {G : SimpleGraph X} {N : G.Subgraph}
    (hN : N.IsMatching) : N.verts.ncard = 2*N.edgeSet.ncard := by
  classical
  let := Fintype.ofFinite X
  have cardEq : N.coe.edgeSet.ncard = N.edgeSet.ncard :=
    calc N.coe.edgeSet.ncard = (Sym2.map ((↑) : N.verts → X) '' N.coe.edgeSet).ncard :=
           (Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)).symm
         _ = _ := congrArg Set.ncard N.image_coe_edgeSet_coe
  exact (matching_count_aux hN).trans (congrArg (2 * ·) cardEq)

theorem tutteJoin_perfect_le {X : Type*} [Finite X] (G : SimpleGraph X) (d : ℕ)
    (perfect : ∃ M : (tutteJoin G d).Subgraph, M.IsPerfectMatching) :
    Nat.card X ≤ 2*matchingEdges G + d := by
  obtain ⟨M, hm⟩ := perfect
  let N := tutteJoinRestrict M
  have hN := tutteJoinRestrict_isMatching hm.1
  have covered := matching_vertices_eq_twice_edges hN
  have missed := tutteJoinRestrict_missed_le hm
  have maxbound := le_matchingEdges hN
  have total := Set.ncard_sdiff_add_ncard_of_subset (s := N.verts) (t := Set.univ) N.verts.subset_univ
  have parts : Nat.card {v : X // v ∉ N.verts} + N.verts.ncard = Nat.card X := by
    have eqset : (Set.univ \ N.verts : Set X) = N.vertsᶜ := by ext; simp
    rw [eqset, Set.ncard_univ] at total
    exact total
  dsimp only [N] at parts
  omega

#print axioms tutteJoin
#print axioms tutteJoinRestrict_isMatching
#print axioms tutteJoinRestrict_missed_le
#print axioms matching_vertices_eq_twice_edges
#print axioms tutteJoin_perfect_le
end JSP452Audit.StarHost
