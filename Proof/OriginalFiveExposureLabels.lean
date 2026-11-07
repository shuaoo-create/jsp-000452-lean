import FourSixRegularComponentsExcluded
namespace JSP452Audit.StarHost
open SimpleGraph

structure FiveExposureLabels {X:Type*} [Finite X] (G:SimpleGraph X) where
  M : G.Subgraph
  matching : M.IsMatching
  maximum : M.edgeSet.ncard=matchingEdges G
  optimal : (exposedFull G M 5).ncard=minimumExposure G 5
  tip : ↥(exposedFull G M 5)→X
  attached : ∀u,G.Adj u.val (tip u)

theorem five_exposure_labels_exist {X:Type*} [Finite X] (G:SimpleGraph X) : Nonempty (FiveExposureLabels G) := by
  obtain ⟨M,hm,best,optimal⟩ := minimumExposure_attained G 5
  have neighbor (u:↥(exposedFull G M 5)) : (G.neighborSet u.val).Nonempty := by
    have size : (G.neighborSet u.val).ncard=5 := u.property.2
    exact (Set.ncard_pos (G.neighborSet u.val).toFinite).mp (by omega)
  choose tip edge using neighbor
  exact ⟨⟨M,hm,best,optimal,tip,edge⟩⟩

namespace FiveExposureLabels
variable {X:Type*} [Finite X] {G:SimpleGraph X} (L:FiveExposureLabels G)
abbrev W := exposedFull G L.M 5

theorem tip_matched (u:↥L.W) : L.tip u∈L.M.verts :=
  missed_neighbors_subset G L.M L.matching L.maximum u.property.1 (L.attached u)

def selected (A:Set ↥L.W) : SimpleGraph X where
  Adj x y := (∃u∈A,u.val=x ∧ L.tip u=y) ∨ (∃u∈A,u.val=y ∧ L.tip u=x)
  symm := ⟨fun _ _ e => e.symm⟩
  loopless := ⟨fun x e => by
    rcases e with ⟨u,_,hx,tx⟩|⟨u,_,hx,tx⟩ <;> exact (L.attached u).ne (hx.trans tx.symm)⟩

theorem selected_sub (A:Set ↥L.W) : L.selected A≤G := by
  rintro x y (⟨u,_,rfl,rfl⟩|⟨u,_,rfl,rfl⟩)
  · exact L.attached u
  · exact (L.attached u).symm

def fiber (A:Set ↥L.W) (v:X) : Set ↥L.W := {u|u∈A ∧ L.tip u=v}

theorem selected_at_matched (A:Set ↥L.W) {v:X} (hv:v∈L.M.verts) :
    (L.selected A).neighborSet v=Subtype.val '' L.fiber A v := by
  ext x
  constructor
  · rintro (⟨u,_,uv,_⟩|⟨u,ua,ux,tip⟩)
    · exact (u.property.1 (uv ▸ hv)).elim
    · exact ⟨u,⟨ua,tip⟩,ux⟩
  · rintro ⟨u,⟨ua,tip⟩,rfl⟩
    exact Or.inr ⟨u,ua,rfl,tip⟩

theorem selected_at_unmatched (A:Set ↥L.W) {v:X} (away:v∉L.M.verts) :
    (L.selected A).neighborSet v= {x|∃u∈A,u.val=v ∧ L.tip u=x} := by
  ext x
  constructor
  · rintro (h|⟨u,_,_,tip⟩)
    · exact h
    · exact (away (tip ▸ L.tip_matched u)).elim
  · exact Or.inl

theorem selected_unmatched_degree (A:Set ↥L.W) {v:X} (away:v∉L.M.verts) :
    ((L.selected A).neighborSet v).ncard≤1 := by
  rw [L.selected_at_unmatched A away]
  apply (Set.ncard_le_one (Set.toFinite _)).mpr
  rintro x ⟨u,_,uv,tx⟩ y ⟨w,_,wv,ty⟩
  have same : u=w := Subtype.ext (uv.trans wv.symm)
  exact tx.symm.trans ((congrArg L.tip same).trans ty)

#print axioms tip_matched
#print axioms selected_sub
#print axioms selected_at_matched
#print axioms selected_at_unmatched
#print axioms selected_unmatched_degree
end FiveExposureLabels
#print axioms five_exposure_labels_exist
end JSP452Audit.StarHost
