import FourMatchedLabels
import ZeroOriginalLabels
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem actual_four_matched_labels (Q : SimpleGraph X) (I W Z : Set X) (conn : Q.Connected)
    (ind : Q.IsIndepSet I) (roots : 2≤I.ncard) (zi : Disjoint I Z) (wz : Disjoint W Z)
    (cover : I∪W∪Z=Set.univ) (size : Z.ncard=4) (reg : ∀x,Nat.card (Q.neighborSet x)=4)
    (one : ∀z∈Z,(Q.neighborSet z∩I).ncard=1) (external : ∀z∈Z,∀y,Q.Adj z y → y∉Z → y∈I)
    (holeNeighbors : ∀w∈W,Q.neighborSet w⊆I) :
    ∃(i:I) (z z₀:Z) (a b:W) (p q:I),Q.Adj z.val i.val ∧ z≠z₀ ∧ a≠b ∧
      Q.Adj i.val a.val ∧ Q.Adj i.val b.val ∧ p≠i ∧ q≠i ∧ p≠q ∧
      Q.Adj a.val p.val ∧ Q.Adj b.val q.val ∧
      ∀j:I,j≠i → let L := ({u:Z|Q.Adj j.val u.val} \ {z₀}).ncard +
        ({w:W|Q.Adj j.val w.val}∩{a,b}).ncard
        L≤3 ∧ (L=3 → j=p ∨ j=q) := by
  classical
  let _ : Nonempty I := (Set.nonempty_of_ncard_ne_zero (by omega : I.ncard≠0)).to_subtype
  let _ : Nonempty Z := (Set.nonempty_of_ncard_ne_zero (by omega : Z.ncard≠0)).to_subtype
  have get (z : Z) : ∃i : I,Q.Adj z.val i.val ∧ ∀j : I,Q.Adj z.val j.val → j=i := by
    have non : (Q.neighborSet z.val ∩ I).Nonempty :=
      (Set.ncard_pos (Set.toFinite _)).mp (by rw [one z.val z.property];decide)
    obtain ⟨a,adj,ai⟩ := non
    refine ⟨⟨a,ai⟩,adj,?_⟩
    intro j edge
    exact Subtype.ext ((Set.ncard_le_one (Set.toFinite _)).mp (one z.val z.property).le
      j.val ⟨edge,j.property⟩ a ⟨adj,ai⟩)
  choose f selected unique using get
  have same (j : I) : ownerFiber f j={u : Z| Q.Adj j.val u.val} := by
    ext z
    exact ⟨fun h => (show f z=j from h) ▸ (selected z).symm,fun h => (unique z j h.symm).symm⟩
  let A (j : I) := {w : W| Q.Adj j.val w.val}
  have img {T : Set X} (j : I) : Subtype.val '' {u:T|Q.Adj j.val u.val}=Q.neighborSet j.val∩T := by
    ext a
    exact ⟨fun ⟨u,adj,eq⟩ => eq ▸ ⟨adj,u.property⟩,fun h => ⟨⟨a,h.2⟩,h.1,rfl⟩⟩
  have fiberCount (j : I) : (ownerFiber f j).ncard=(Q.neighborSet j.val∩Z).ncard := by
    rw [same,←img (T:=Z) j,Set.ncard_image_of_injective _ Subtype.val_injective]
  have degree (j : I) : (ownerFiber f j).ncard+(A j).ncard=4 := by
    have wh : (A j).ncard=(Q.neighborSet j.val∩W).ncard := by
      rw [←img (T:=W) j,Set.ncard_image_of_injective _ Subtype.val_injective]
    have eq : (Q.neighborSet j.val∩Z)∪(Q.neighborSet j.val∩W)=Q.neighborSet j.val := by
      apply Set.Subset.antisymm (Set.union_subset Set.inter_subset_left Set.inter_subset_left)
      intro a adj
      have ac : a∈I∪W∪Z := cover ▸ Set.mem_univ _
      rcases ac with (ai|aw)|az
      · exact (ind j.property ai (show Q.Adj j.val a from adj).ne adj).elim
      · exact Or.inr ⟨adj,aw⟩
      · exact Or.inl ⟨adj,az⟩
    rw [fiberCount,wh,←Set.ncard_union_eq (wz.symm.mono Set.inter_subset_right Set.inter_subset_right),eq]
    exact reg j.val
  have notAll (j : I) : (ownerFiber f j).ncard<4 := by
    rw [fiberCount]
    exact no_single_root_owns_zero_clique Q conn I Z zi roots 4 size reg one external j.val j.property
  have holes (w : W) : {j:I|w∈A j}.ncard=4 := by
    have image : Subtype.val '' {j:I|w∈A j}=Q.neighborSet w.val := by
      ext x
      constructor
      · rintro ⟨j,h,eq⟩
        exact eq ▸ (show Q.Adj j.val w.val from h).symm
      · intro adj
        exact ⟨⟨x,holeNeighbors w.val w.property adj⟩,(show Q.Adj w.val x from adj).symm,rfl⟩
    rw [←Set.ncard_image_of_injective _ Subtype.val_injective,image]
    exact reg w.val
  obtain ⟨i,z,z₀,a,b,p,q,own,diff,ab,ai,bi,pi,qi,pq,ap,bq,cap⟩ :=
    select_four_matched_labels f A (by rwa [Nat.card_coe_set_eq]) degree notAll holes
  refine ⟨i,z,z₀,a,b,p,q,own ▸ selected z,diff,ab,ai,bi,pi,qi,pq,
    (show Q.Adj p.val a.val from ap).symm,(show Q.Adj q.val b.val from bq).symm,?_⟩
  intro j ji
  have bound := cap j ji
  dsimp only [survivingRootLoad,A] at bound
  rwa [same] at bound

#print axioms actual_four_matched_labels
end JSP452Audit.StarHost
