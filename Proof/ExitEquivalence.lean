import MaximalBarrier
import FactorCriticalPeak
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- The unique kind of exit a residual odd component needs in a tight cut:
one matched edge to a named root, or one named exposed original vertex. -/
def IsBarrierExit (G : SimpleGraph X) (S : Set X) (M : G.Subgraph)
    (c : (G.induce Sᶜ).ConnectedComponent) : (↥S ⊕ ↥(M.vertsᶜ : Set X)) → Prop
  | .inl s => ∃ x : ↥(Sᶜ : Set X), x ∈ c.supp ∧ M.Adj x.val s.val
  | .inr u => ∃ x : ↥(Sᶜ : Set X), x ∈ c.supp ∧ x.val=u.val

theorem barrier_exit_component_unique (G : SimpleGraph X) (S : Set X) (M : G.Subgraph)
    (hm : M.IsMatching) {c d : (G.induce Sᶜ).ConnectedComponent}
    (z : ↥S ⊕ ↥(M.vertsᶜ : Set X)) (p : IsBarrierExit G S M c z) (q : IsBarrierExit G S M d z) : c=d := by
  have same (a b : ↥(Sᶜ : Set X)) (ac : a∈c.supp) (bd : b∈d.supp) (eq : a.val=b.val) : c=d := by
    have ab : a=b := Subtype.ext eq
    subst b
    exact ac.symm.trans bd
  cases z with
  | inl s =>
    obtain ⟨a,ac,edge⟩ := p
    obtain ⟨b,bd,edge'⟩ := q
    exact same a b ac bd (hm.eq_of_adj_right edge edge')
  | inr u =>
    obtain ⟨a,ac,id⟩ := p
    obtain ⟨b,bd,id'⟩ := q
    exact same a b ac bd (id.trans id'.symm)

/-- Where the number of names is exact, even an arbitrary choice of one exit
per component exhausts all of them, so no additional exits are possible. -/
theorem matched_exit_equiv_of_count [Finite X] (G : SimpleGraph X) (S : Set X) (M : G.Subgraph)
    (hm : M.IsMatching)
    (existsExit : ∀ c, ∃ z, IsBarrierExit G S M c z)
    (count : Nat.card ((G.induce Sᶜ).ConnectedComponent) = Nat.card (↥S ⊕ ↥(M.vertsᶜ : Set X))) :
    ∃ e : (G.induce Sᶜ).ConnectedComponent ≃ (↥S ⊕ ↥(M.vertsᶜ : Set X)),
      ∀ c z, IsBarrierExit G S M c z ↔ e c=z := by
  classical
  let f c := (existsExit c).choose
  have valid c : IsBarrierExit G S M c (f c) := (existsExit c).choose_spec
  have inj : Function.Injective f := by
    intro c d h
    exact barrier_exit_component_unique G S M hm _ (valid c) (h.symm ▸ valid d)
  have surj : Function.Surjective f := (Nat.bijective_iff_injective_and_card f).2 ⟨inj,count⟩ |>.2
  let e := Equiv.ofBijective f ⟨inj,surj⟩
  refine ⟨e,fun c z => ⟨?_,?_⟩⟩
  · intro cz
    obtain ⟨d,hit⟩ := surj z
    have eq := barrier_exit_component_unique G S M hm z cz (hit ▸ valid d)
    exact eq.symm ▸ hit
  · rintro rfl
    exact valid c
#print axioms matched_exit_equiv_of_count
end JSP452Audit.StarHost