import ZeroCutLabels
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Select the cut labels on the original graph from its actual partition
and adjacency. Each remaining root sees at most D−2 of the retained
clique and the two retained holes. -/
theorem actual_zero_cut_labels (Q : SimpleGraph X) (I W Z : Set X) (D : ℕ) (large : 6≤D)
    (conn : Q.Connected) (ind : Q.IsIndepSet I) (roots : 2≤I.ncard)
    (zi : Disjoint I Z) (wz : Disjoint W Z) (cover : I∪W∪Z=Set.univ)
    (size : Z.ncard=D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (one : ∀z∈Z,(Q.neighborSet z∩I).ncard=1)
    (external : ∀z∈Z,∀y,Q.Adj z y → y∉Z → y∈I) :
    ∃(i : I) (z z₀ : Z) (w₁ w₂ : W), Q.Adj z.val i.val ∧ z≠z₀ ∧ w₁≠w₂ ∧
      Q.Adj i.val w₁.val ∧ Q.Adj i.val w₂.val ∧
      ∀j : I,j≠i → ({u : Z | Q.Adj j.val u.val} \ {z₀}).ncard +
        ({w : W | Q.Adj j.val w.val} ∩ {w₁,w₂}).ncard ≤ D-2 := by
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
  have degree (j : I) : (ownerFiber f j).ncard+(A j).ncard=D := by
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
  have notAll (j : I) : (ownerFiber f j).ncard<D := by
    rw [fiberCount]
    exact no_single_root_owns_zero_clique Q conn I Z zi roots D size reg one external j.val j.property
  obtain ⟨i,z,z₀,w₁,w₂,owner,diff,dw,iw₁,iw₂,cost⟩ :=
    select_zero_deletion_labels f A D large (by rwa [Nat.card_coe_set_eq]) degree notAll
  refine ⟨i,z,z₀,w₁,w₂,owner ▸ selected z,diff,dw,iw₁,iw₂,?_⟩
  intro j ji
  have c := cost j ji
  dsimp only [survivingRootLoad,A] at c
  rwa [same] at c

#print axioms actual_zero_cut_labels
end JSP452Audit.StarHost
