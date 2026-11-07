import ZeroCliqueRootDegree
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- No one root owns the entire D-clique: that clique plus the root would
be closed under all graph edges, despite a distinct independent-set vertex. -/
theorem no_single_root_owns_zero_clique (Q : SimpleGraph X) (conn : Q.Connected)
    (I Z : Set X) (dis : Disjoint I Z) (roots : 2≤I.ncard) (D : ℕ) (size : Z.ncard=D)
    (reg : ∀u,Nat.card (Q.neighborSet u)=D)
    (one : ∀x∈Z,(Q.neighborSet x∩I).ncard=1)
    (external : ∀x∈Z,∀y,Q.Adj x y → y∉Z → y∈I)
    (p : X) (hp : p∈I) : (Q.neighborSet p∩Z).ncard<D := by
  classical
  have upper : (Q.neighborSet p∩Z).ncard≤D := (Set.ncard_le_ncard Set.inter_subset_right).trans_eq size
  by_contra! high
  have all : Q.neighborSet p∩Z=Z :=
    Set.eq_of_subset_of_ncard_le Set.inter_subset_right (by omega)
  have into : Z⊆Q.neighborSet p := fun x h => (show x∈Q.neighborSet p∩Z by rw [all];exact h).1
  have eq : Z=Q.neighborSet p := Set.eq_of_subset_of_ncard_le into
    (show (Q.neighborSet p).ncard≤Z.ncard by rw [←Nat.card_coe_set_eq,reg,size])
  let U := insert p Z
  have closed {a b : X} (ha : a∈U) (edge : Q.Adj a b) : b∈U := by
    rcases ha with h|az
    · subst a
      exact Or.inr (eq ▸ (show b∈Q.neighborSet p from edge))
    · by_cases bz : b∈Z
      · exact Or.inr bz
      · have bi := external a az b edge bz
        have small := (Set.ncard_le_one (Set.toFinite (Q.neighborSet a∩I))).mp (Nat.le_of_eq (one a az))
        have ap : Q.Adj a p := (show Q.Adj p a from into az).symm
        exact Or.inl (small b ⟨edge,bi⟩ p ⟨ap,hp⟩)
  have travel {u v} (walk : Q.Walk u v) : u∈U → v∈U := by
    induction walk with
    | nil => exact id
    | cons e _ ih => exact fun h => ih (closed h e)
  have inU (q : X) : q∈U := by
    obtain ⟨walk⟩ := conn.preconnected p q
    exact travel walk (Or.inl rfl)
  have subset : I⊆{p} := by
    intro q hq
    exact (inU q).resolve_right (Set.disjoint_left.mp dis hq)
  have narrow := Set.ncard_le_ncard subset
  rw [Set.ncard_singleton] at narrow
  omega

#print axioms no_single_root_owns_zero_clique
end JSP452Audit.StarHost
