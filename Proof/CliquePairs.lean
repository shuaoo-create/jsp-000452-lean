import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.SetTheory.Cardinal.Finite

namespace JSP452Audit.Padded

/-- An even finite set is partitioned into pairs by transporting the swap
    of two equal-size summands. This includes the empty index type. -/
private theorem existsPairing (T : Type*) [Finite T] (even : Even (Nat.card T)) :
    ∃ p : T → T, (∀ i, p (p i) = i) ∧ (∀ i, i ≠ p i) := by
  classical
  let _ := Fintype.ofFinite T
  obtain ⟨k, hk⟩ := even
  let eqv : T ≃ Fin k ⊕ Fin k := Fintype.equivOfCardEq (by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_fin] using hk)
  let p (i : T) : T := eqv.symm (Sum.swap (eqv i))
  refine ⟨p, ?_, ?_⟩
  · intro i
    simp [p]
  · intro i h
    have hs : eqv i = Sum.swap (eqv i) := by simpa [p] using congrArg eqv h
    cases hi : eqv i <;> simp [hi] at hs

/-- Match the whole embedded clique, leaving every vertex outside its range out
    of the subgraph. The ambient graph need not itself be complete or finite. -/
theorem existsMatchingOnEvenClique {V T : Type*} [Finite T] (G : SimpleGraph V)
    (e : T ↪ V) (clique : ∀ ⦃i j : T⦄, i ≠ j → G.Adj (e i) (e j))
    (even : Even (Nat.card T)) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = Set.range e := by
  obtain ⟨p, involutive, noSelf⟩ := existsPairing T even
  let M : G.Subgraph := {
    verts := Set.range e
    Adj := fun x y => ∃ i : T, e i = x ∧ e (p i) = y
    adj_sub := by
      rintro x y ⟨i, rfl, rfl⟩
      exact clique (noSelf i)
    edge_vert := by
      rintro x y ⟨i, hx, _⟩
      exact ⟨i, hx⟩
    symm := ⟨by
      rintro x y ⟨i, rfl, rfl⟩
      exact ⟨p i, rfl, congrArg e (involutive i)⟩⟩ }
  refine ⟨M, ?_, rfl⟩
  rintro x ⟨i, rfl⟩
  refine ⟨e (p i), ⟨i, rfl, rfl⟩, ?_⟩
  rintro y ⟨j, hji, hjy⟩
  exact hjy.symm.trans (congrArg (fun t => e (p t)) (e.injective hji))

#print axioms existsMatchingOnEvenClique
end JSP452Audit.Padded
