import RetainedBoundary

namespace JSP452Audit.Padded
open SimpleGraph JSP452Audit.StarHost

variable {X : Type*} [DecidableEq X] (H : SimpleGraph X) (W : Finset X) (x : X)

private abbrev enlarged := H.induce (↑(insert x W) : Set X)
private def added : ↥(↑(insert x W) : Set X) := ⟨x,Finset.mem_insert_self _ _⟩

private def undoInsert (outside : x ∉ W) :
    (enlarged H W x).induce {a | a ≠ added W x} ≃g H.induce (W : Set X) where
  toFun a := ⟨a.val.val, by
    have h : a.val.val=x ∨ a.val.val∈W := Finset.mem_insert.mp a.val.property
    exact h.resolve_left (fun eq => a.property (Subtype.ext eq))⟩
  invFun a := ⟨⟨a.val,Finset.mem_insert_of_mem a.property⟩,
    fun eq => by
      have same : a.val=x := congrArg Subtype.val eq
      exact outside (same ▸ a.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := Iff.rfl

theorem restore_actual_vertex [Finite X] (outside : x ∉ W)
    (two : (retainedNeighborComponents H W x).ncard ≤ 2) :
    retainedScore H W ≤ retainedScore H (insert x W) := by
  classical
  let e := undoInsert H W x outside
  let A := enlarged H W x
  let v := added W x
  let old := A.induce {a | a ≠ v}
  have send (c : old.ConnectedComponent) (hc : componentTouches A v c) :
      e.connectedComponentEquiv c ∈ retainedNeighborComponents H W x := by
    obtain ⟨w,member,edge⟩ := hc
    refine ⟨e w,edge.symm,?_⟩
    have he : old.connectedComponentMk w = c := member
    rw [← he]
    rfl
  let lift (a : {c | componentTouches A v c}) : retainedNeighborComponents H W x :=
    ⟨e.connectedComponentEquiv a.val, send _ a.property⟩
  have inj : Function.Injective lift := by
    intro a b h
    exact Subtype.ext (e.connectedComponentEquiv.injective
      (congrArg (fun z : retainedNeighborComponents H W x => z.val) h))
  have bound : {c | componentTouches A v c}.ncard ≤ (retainedNeighborComponents H W x).ncard :=
    Nat.card_le_card_of_injective lift inj
  have gain := restore_two_components A v (bound.trans two)
  have same := odd_ncard_iso e
  change old.oddComponents.ncard = (H.induce (W : Set X)).oddComponents.ncard at same
  change old.oddComponents.ncard ≤ A.oddComponents.ncard + 1 at gain
  rw [same] at gain
  unfold retainedScore
  rw [Finset.card_insert_of_notMem outside]
  change _ ≤ A.oddComponents.ncard + (W.card+1)
  omega

theorem maximal_cut_obstruction [Finite X] :
    ∃ U : Finset X, (∀ V, retainedScore H V ≤ retainedScore H U) ∧
      ∀ z, z ∉ U → 2 < (retainedNeighborComponents H U z).ncard := by
  classical
  obtain ⟨U,top,strict⟩ := extremal_retained H
  refine ⟨U,top,?_⟩
  intro z outside
  by_contra! few
  exact (not_lt_of_ge (restore_actual_vertex H U z outside few))
    (strict z (insert z U) outside (fun _ => Finset.mem_insert))

#print axioms restore_actual_vertex
#print axioms maximal_cut_obstruction
end JSP452Audit.Padded
