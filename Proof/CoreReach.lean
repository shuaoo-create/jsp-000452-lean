import CoreLanguage

namespace JSP452Audit.Padded
open SimpleGraph

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]
variable {S T : Set V}

/-- A retained stub at u reaches the anchor through the mandatory token at u. -/
theorem Spec.core_stub_reaches_anchor (u : P.CorePoint S T) (s : P.Stub) (owner : s.1 = u.val)
    (keep : (Sum.inl s : P.Vertex) ∈ P.canonicalKept S T) :
    (P.canonGraph S T).Reachable ⟨.inl s,keep⟩ (P.coreAnchor u) := by
  have left : (P.canonGraph S T).Adj ⟨.inl s,keep⟩ (P.coreMandatory u) := owner.symm
  have right : (P.canonGraph S T).Adj (P.coreMandatory u) (P.coreAnchor u) := rfl
  exact left.reachable.trans right.reachable

/-- Each original edge in the core gives an anchor-to-anchor walk by
going to its two real stubs and crossing their edge. -/
theorem Spec.core_adj_anchors_reachable {u w : P.CorePoint S T} (e : (P.coreGraph S T).Adj u w) :
    (P.canonGraph S T).Reachable (P.coreAnchor u) (P.coreAnchor w) := by
  let a : P.CanonVertex S T := P.canonicalPoint (P.realStub u.val w.val e)
    (fun h => u.property (Or.inl h))
  let b : P.CanonVertex S T := P.canonicalPoint (P.realStub w.val u.val e.symm)
    (fun h => w.property (Or.inl h))
  have left : (P.canonGraph S T).Reachable a (P.coreAnchor u) :=
    P.core_stub_reaches_anchor u ⟨u.val,.inl ⟨w.val,e⟩⟩ rfl a.property
  have middle : (P.canonGraph S T).Adj a b := ⟨rfl,rfl⟩
  have right : (P.canonGraph S T).Reachable b (P.coreAnchor w) :=
    P.core_stub_reaches_anchor w ⟨w.val,.inl ⟨u.val,e.symm⟩⟩ rfl b.property
  exact left.symm.trans (middle.reachable.trans right)

/-- Lift reachability between any two labels in the same original component. -/
theorem Spec.core_anchors_reachable (C : P.CoreComponent S T) {u w : P.CorePoint S T}
    (hu : u ∈ C.supp) (hw : w ∈ C.supp) :
    (P.canonGraph S T).Reachable (P.coreAnchor u) (P.coreAnchor w) := by
  have r := C.reachable_of_mem_supp hu hw
  rw [reachable_iff_reflTransGen] at r
  clear hw
  induction r with
  | refl => exact .rfl
  | tail _ e ih => exact ih.trans (P.core_adj_anchors_reachable e)

/-- In an attached T-stub, the stored neighbor is the actual core vertex.
The opposite real stub links it back to that vertex's block. -/
theorem Spec.onCore_reaches_anchor (C : P.CoreComponent S T) {z : P.CanonVertex S T}
    (hz : P.onCore C z.val) :
    ∃ u : P.CorePoint S T, u ∈ C.supp ∧
      (P.canonGraph S T).Reachable z (P.coreAnchor u) := by
  rcases z with ⟨⟨v,w | i⟩ | ((a | b) | g),keep⟩
  · rcases hz with ⟨hu,hC⟩ | ⟨_,hu,hC⟩
    · exact ⟨⟨v,hu⟩,hC,P.core_stub_reaches_anchor ⟨v,hu⟩ ⟨v,.inl w⟩ rfl keep⟩
    · let u : P.CorePoint S T := ⟨w.val,hu⟩
      let a : P.CanonVertex S T := P.canonicalPoint (P.realStub w.val v w.property.symm)
        (fun h => hu (Or.inl h))
      have step : (P.canonGraph S T).Adj ⟨P.realStub v w.val w.property,keep⟩ a := ⟨rfl,rfl⟩
      have rest : (P.canonGraph S T).Reachable a (P.coreAnchor u) :=
        P.core_stub_reaches_anchor u ⟨w.val,.inl ⟨v,w.property.symm⟩⟩ rfl a.property
      exact ⟨u,hC,step.reachable.trans rest⟩
  · obtain ⟨hu,hC⟩ := hz
    exact ⟨⟨v,hu⟩,hC,P.core_stub_reaches_anchor ⟨v,hu⟩ ⟨v,.inr i⟩ rfl keep⟩
  · obtain ⟨hu,hC⟩ := hz
    let u : P.CorePoint S T := ⟨a.1,hu⟩
    have step : (P.canonGraph S T).Adj ⟨P.mandatory a,keep⟩ (P.coreAnchor u) := rfl
    exact ⟨u,hC,step.reachable⟩
  · obtain ⟨hu,hC⟩ := hz
    let u : P.CorePoint S T := ⟨b.1,hu⟩
    have step : (P.canonGraph S T).Adj ⟨P.optional b,keep⟩ (P.coreAnchor u) := rfl
    exact ⟨u,hC,step.reachable⟩
  · exact hz.elim

/-- All retained labels over one original component are in one auxiliary component. -/
theorem Spec.onCore_reachable (C : P.CoreComponent S T) {z z' : P.CanonVertex S T}
    (hz : P.onCore C z.val) (hz' : P.onCore C z'.val) :
    (P.canonGraph S T).Reachable z z' := by
  obtain ⟨u,hu,zu⟩ := P.onCore_reaches_anchor C hz
  obtain ⟨w,hw,z'w⟩ := P.onCore_reaches_anchor C hz'
  exact zu.trans ((P.core_anchors_reachable C hu hw).trans z'w.symm)

#print axioms Spec.core_adj_anchors_reachable
#print axioms Spec.core_anchors_reachable
#print axioms Spec.onCore_reaches_anchor
#print axioms Spec.onCore_reachable
end JSP452Audit.Padded
