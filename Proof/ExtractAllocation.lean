import RootAllocation
namespace JSP452Audit.StarHost
open SimpleGraph

theorem extract_root_allocation {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (M : G.Subgraph) (D : ℕ)
    (e : (G.induce Sᶜ).ConnectedComponent ≃ (↥S ⊕ ↥(M.vertsᶜ : Set X)))
    (names : ∀ c z, IsBarrierExit G S M c z ↔ e c=z) :
    ∃ A : RootAllocation G S, (freeFull G S D A).ncard ≤ (exposedFull G M D).ncard := by
  classical
  let place : ↥S ↪ (G.induce Sᶜ).ConnectedComponent :=
    ⟨fun s => e.symm (.inl s),fun _ _ eq => Sum.inl.inj (e.symm.injective eq)⟩
  have link (a : S) : ∃ z : (place a).supp, G.Adj a.val z.val.val := by
    have paired := (names (place a) (.inl a)).2 (e.apply_symm_apply _)
    obtain ⟨v,part,edge⟩ := paired
    exact ⟨⟨v,part⟩,(M.adj_sub edge).symm⟩
  let A : RootAllocation G S := ⟨place,link⟩
  have witness (c : freeFull G S D A) :
      ∃ z : exposedFull G M D, e c.val = .inr ⟨z.val,z.property.1⟩ := by
    cases eq : e c.val with
    | inl s =>
      have used : c.val∈Set.range A.place := ⟨s,by change e.symm (.inl s)=c.val; rw [← eq,e.symm_apply_apply]⟩
      exact (c.property.1 used).elim
    | inr u =>
      obtain ⟨v,part,uid⟩ := (names c.val _).2 eq
      have high := c.property.2 ⟨v,part⟩
      change Nat.card (G.neighborSet v.val)=D at high
      rw [uid] at high
      exact ⟨⟨u.val,u.property,high⟩,rfl⟩
  let f (c : freeFull G S D A) : exposedFull G M D := (witness c).choose
  have inj : Function.Injective f := by
    intro c d eq
    have a := (witness c).choose_spec
    have b := (witness d).choose_spec
    apply Subtype.ext
    apply e.injective
    rw [a,b]
    have raw : (f c).val = (f d).val := congrArg (fun z : exposedFull G M D => z.val) eq
    exact congrArg Sum.inr (Subtype.ext raw)
  exact ⟨A,Nat.card_le_card_of_injective f inj⟩
#print axioms extract_root_allocation
end JSP452Audit.StarHost