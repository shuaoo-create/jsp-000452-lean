import MatchingShadow

namespace JSP452Audit.Padded
variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

private theorem mandatory_mem_has_local_mate (M : P.graph.Subgraph) (hM : M.IsMatching)
    (v : V) (i : Fin (P.mandatoryCount v)) (hi : P.mandatory ⟨v, i⟩ ∈ M.verts) :
    ∃ a : P.G.neighborSet v ⊕ Fin (P.padding v),
      M.Adj (.inl ⟨v, a⟩) (P.mandatory ⟨v, i⟩) := by
  obtain ⟨w, hw, _⟩ := hM hi
  cases w with
  | inl s =>
    obtain ⟨u, a⟩ := s
    have hv : v = u := (P.stub_adj_mandatory_iff _ _).mp (M.adj_sub hw.symm)
    subst u
    exact ⟨a, hw.symm⟩
  | inr t =>
    exact (M.adj_sub hw).1.elim

private theorem mandatoryAt_injective (v : V) :
    Function.Injective (fun i : Fin (P.mandatoryCount v) => P.mandatory ⟨v, i⟩) := by
  intro i j h
  have he : (⟨v, i⟩ : P.Mandatory) = ⟨v, j⟩ :=
    Sum.inl.inj (Sum.inl.inj (Sum.inr.inj h))
  exact eq_of_heq (Sigma.mk.inj he).2

/-- Each occupied mandatory token and each red neighbor needs a distinct local
stub. Subtracting the red cap therefore charges its excess to exposed tokens. -/
theorem Spec.redExcess_le_unmatchedMandatory (M : P.graph.Subgraph) (hM : M.IsMatching)
    (v : V) :
    Nat.card ((P.redShadow M).neighborSet v) - P.A v ≤
      Nat.card {i : Fin (P.mandatoryCount v) // P.mandatory ⟨v, i⟩ ∉ M.verts} := by
  classical
  let Used := {i : Fin (P.mandatoryCount v) // P.mandatory ⟨v, i⟩ ∈ M.verts}
  let Local := P.G.neighborSet v ⊕ Fin (P.padding v)
  let mate : Used → Local := fun i =>
    (mandatory_mem_has_local_mate P M hM v i.val i.property).choose
  have hm (i : Used) : M.Adj (.inl ⟨v, mate i⟩) (P.mandatory ⟨v, i.val⟩) :=
    (mandatory_mem_has_local_mate P M hM v i.val i.property).choose_spec
  let redSlot : (P.redShadow M).neighborSet v → Local :=
    fun w => .inl ⟨w.val, P.redShadow_le M w.property⟩
  have injRed : Function.Injective redSlot := by
    intro a b h
    have e : (⟨a.val, P.redShadow_le M a.property⟩ : P.G.neighborSet v) =
        ⟨b.val, P.redShadow_le M b.property⟩ := Sum.inl.inj h
    exact Subtype.ext (congrArg (fun z : P.G.neighborSet v => z.val) e)
  have injMate : Function.Injective mate := by
    intro i j h
    have hi := hm i
    rw [h] at hi
    exact Subtype.ext (mandatoryAt_injective P v (hM.eq_of_adj_left hi (hm j)))
  have disjointSlots (w : (P.redShadow M).neighborSet v) (i : Used) : redSlot w ≠ mate i := by
    intro he
    have bad := hm i
    rw [← he] at bad
    exact P.cross_used_blocks_token M hM (P.redShadow_le M w.property) w.property
      (.inl (.inl ⟨v, i.val⟩)) bad
  have hi : Function.Injective (Sum.elim redSlot mate) := by
    intro a b h
    obtain a | a := a <;> obtain b | b := b
    · exact congrArg Sum.inl (injRed h)
    · exact (disjointSlots a b h).elim
    · exact (disjointSlots b a h.symm).elim
    · exact congrArg Sum.inr (injMate h)
  have bound := Nat.card_le_card_of_injective _ hi
  change Nat.card ((P.redShadow M).neighborSet v ⊕ Used) ≤
    Nat.card (P.G.neighborSet v ⊕ Fin (P.padding v)) at bound
  rw [Nat.card_sum, Nat.card_sum, Nat.card_fin, Nat.card_eq_fintype_card (α := P.G.neighborSet v),
    P.G.card_neighborSet_eq_degree] at bound
  have split := Nat.card_congr (Equiv.sumCompl
    (fun i : Fin (P.mandatoryCount v) => P.mandatory ⟨v, i⟩ ∈ M.verts))
  rw [Nat.card_sum, Nat.card_fin] at split
  change Nat.card Used + Nat.card {i : Fin (P.mandatoryCount v) //
    P.mandatory ⟨v, i⟩ ∉ M.verts} = P.mandatoryCount v at split
  have total : P.mandatoryCount v + P.A v = P.G.degree v + P.padding v := by
    unfold Spec.mandatoryCount Spec.padding
    omega
  omega

#print axioms Spec.redExcess_le_unmatchedMandatory
end JSP452Audit.Padded
