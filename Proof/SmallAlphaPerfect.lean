import OddLocalCritical

namespace JSP452Audit.StarHost
open SimpleGraph

/-- At least one pair in any triple of distinct actual vertices is adjacent. -/
def NoIndependentTriple {X : Type*} (G : SimpleGraph X) : Prop :=
  ∀ x y z : X, x ≠ y → x ≠ z → y ≠ z → G.Adj x y ∨ G.Adj x z ∨ G.Adj y z

theorem NoIndependentTriple.induce {X : Type*} {G : SimpleGraph X} (small : NoIndependentTriple G)
    (U : Set X) : NoIndependentTriple (G.induce U) := by
  intro x y z xy xz yz
  exact small x.val y.val z.val (fun h => xy (Subtype.ext h))
    (fun h => xz (Subtype.ext h)) (fun h => yz (Subtype.ext h))

/-- Three different components yield three different representatives which
are pairwise nonadjacent, including when the components are singletons. -/
theorem odd_components_le_two_of_no_independent_triple {X : Type*} [Finite X]
    (G : SimpleGraph X) (small : NoIndependentTriple G) : G.oddComponents.ncard ≤ 2 := by
  classical
  by_contra! three
  let _ := Fintype.ofFinite G.oddComponents
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Fin 3) ≤ Fintype.card G.oddComponents by
      rw [Fintype.card_fin,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]; omega)
  let rep (i : Fin 3) := (e i).val.nonempty_supp.choose
  have belongs (i : Fin 3) : G.connectedComponentMk (rep i) = (e i).val :=
    (e i).val.nonempty_supp.choose_spec
  have different {i j : Fin 3} (neq : i≠j) : (e i).val ≠ (e j).val := by
    intro same; exact neq (e.injective (Subtype.ext same))
  have dist {i j : Fin 3} (neq : i≠j) : rep i ≠ rep j := by
    intro same; apply different neq
    rw [←belongs,←belongs,same]
  have noEdge {i j : Fin 3} (neq : i≠j) : ¬ G.Adj (rep i) (rep j) := by
    intro edge; apply different neq
    exact (belongs i).symm.trans ((ConnectedComponent.sound edge.reachable).trans (belongs j))
  have e01 : (0 : Fin 3) ≠ 1 := by decide
  have e02 : (0 : Fin 3) ≠ 2 := by decide
  have e12 : (1 : Fin 3) ≠ 2 := by decide
  exact (small _ _ _ (dist e01) (dist e02) (dist e12)).elim (noEdge e01)
    (fun h => h.elim (noEdge e02) (noEdge e12))

/-- In an even-order graph, a Tutte violation would require at least two
more odd components than removed vertices. The independence bound leaves
only the empty cut, which cannot disconnect a preconnected graph. -/
theorem perfect_of_preconnected_even_no_independent_triple {X : Type*} [Finite X]
    (G : SimpleGraph X) (conn : G.Preconnected) (even : Even (Nat.card X))
    (small : NoIndependentTriple G) : ∃ M : G.Subgraph, M.IsPerfectMatching := by
  classical
  apply G.tutte.mpr
  intro S
  rw [tutte_violator_induce]
  intro violation
  have cap := odd_components_le_two_of_no_independent_triple (G.induce Sᶜ) (small.induce _)
  have parity := (G.induce Sᶜ).odd_ncard_oddComponents
  simp only [Nat.odd_iff,Nat.card_coe_set_eq] at parity
  have order := Set.ncard_add_ncard_compl S
  have evenMod := Nat.even_iff.mp even
  have empty := (Set.ncard_eq_zero (Set.toFinite S)).mp (by omega)
  rw [empty,Set.compl_empty,odd_ncard_iso (induceUnivIso G),Set.ncard_empty] at violation
  have parityG := G.odd_ncard_oddComponents
  simp only [Nat.odd_iff] at parityG
  have bounded : G.oddComponents.ncard ≤ 1 :=
    (Set.ncard_le_one (Set.toFinite _)).mpr (fun _ _ _ _ => conn.subsingleton_connectedComponent.elim _ _)
  omega

/-- An odd graph of independence number at most two is factor-critical
whenever all its single-vertex deletions are preconnected. -/
theorem critical_of_odd_small_alpha {X : Type*} [Finite X] (Q : SimpleGraph X)
    (odd : Odd (Nat.card X)) (small : NoIndependentTriple Q)
    (connects : ∀ v : X, (Q.induce {x | x ≠ v}).Preconnected) : PerfectAfterEveryDeletion Q := by
  intro v
  apply perfect_of_preconnected_even_no_independent_triple _ (connects v) _ (small.induce _)
  have eq : {x : X | x ≠ v} = ({v} : Set X)ᶜ := by ext; simp
  rw [Nat.card_coe_set_eq,eq,Set.ncard_compl,Set.ncard_singleton,Nat.even_iff]
  have parity := Nat.odd_iff.mp odd
  omega

#print axioms odd_components_le_two_of_no_independent_triple
#print axioms perfect_of_preconnected_even_no_independent_triple
#print axioms critical_of_odd_small_alpha
end JSP452Audit.StarHost
