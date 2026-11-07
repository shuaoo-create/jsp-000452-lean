import SmallAlphaPerfect
import MaximalUncovered

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- With no independent triple, every independent set on the original
labels has at most two elements. -/
theorem NoIndependentTriple.indepSet_ncard_le_two {G : SimpleGraph X}
    (small : NoIndependentTriple G) (S : Set X) (ind : G.IsIndepSet S) :
    S.ncard ≤ 2 := by
  by_contra! three
  obtain ⟨x,y,z,hx,hy,hz,xy,xz,yz⟩ := (Set.two_lt_ncard_iff (Set.toFinite S)).mp three
  exact (small x y z xy xz yz).elim (ind hx hy xy)
    (fun h => h.elim (ind hx hz xz) (ind hy hz yz))

/-- In odd order the independent holes of an inclusion-maximal matching
have odd cardinality. With independence number at most two, this leaves
exactly one original vertex, and the matching reaches the true rank. -/
theorem odd_small_alpha_maximal_matching (G : SimpleGraph X)
    (odd : Odd (Nat.card X)) (small : NoIndependentTriple G)
    (M : G.Subgraph) (hm : M.IsMatching)
    (maximal : ∀ N : G.Subgraph, N.IsMatching → M ≤ N → M = N) :
    M.edgeSet.ncard = matchingEdges G ∧ M.vertsᶜ.ncard = 1 ∧
      ∃ v : X, M.vertsᶜ = {v} := by
  have independent := (maximal_matching_iff_uncovered_independent G M hm).mp maximal
  have bound := small.indepSet_ncard_le_two M.vertsᶜ independent
  have count := Set.ncard_add_ncard_compl M.verts
  rw [matching_vertices_eq_twice_edges hm] at count
  obtain ⟨r,order⟩ := odd
  have one : M.vertsᶜ.ncard = 1 := by omega
  obtain ⟨N,hn,maximum⟩ := exists_maximum_matching G
  have room := Set.ncard_add_ncard_compl N.verts
  rw [matching_vertices_eq_twice_edges hn,maximum] at room
  exact ⟨le_antisymm (le_matchingEdges hm) (by omega),one,Set.ncard_eq_one.mp one⟩

/-- The same graph is factor-critical when every single-vertex deletion is
preconnected. The matching conclusion itself used no connectivity premise. -/
theorem odd_small_alpha_matching_and_critical (G : SimpleGraph X)
    (odd : Odd (Nat.card X)) (small : NoIndependentTriple G)
    (connects : ∀ v : X, (G.induce {x | x ≠ v}).Preconnected) :
    (∀ M : G.Subgraph, M.IsMatching →
      (∀ N : G.Subgraph, N.IsMatching → M ≤ N → M = N) →
      M.edgeSet.ncard = matchingEdges G ∧ M.vertsᶜ.ncard = 1 ∧
        ∃ v : X, M.vertsᶜ = {v}) ∧ PerfectAfterEveryDeletion G :=
  ⟨fun M hm maximal => odd_small_alpha_maximal_matching G odd small M hm maximal,
    critical_of_odd_small_alpha G odd small connects⟩

#print axioms NoIndependentTriple.indepSet_ncard_le_two
#print axioms odd_small_alpha_maximal_matching
#print axioms odd_small_alpha_matching_and_critical
end JSP452Audit.StarHost
