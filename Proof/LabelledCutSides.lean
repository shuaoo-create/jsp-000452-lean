import ActualCrossingPort
namespace JSP452Audit.StarHost
open SimpleGraph
variable {V : Type*} [Finite V]

/-- Lift the two sides of a cut inside an induced region back onto the
residual graph labels. -/
theorem labelled_cut_sides (H : SimpleGraph V) (P : Set V) (x : P)
    (conn : (H.induce P).Preconnected) (small : NoIndependentTriple (H.induce P))
    (cut : ¬ ((H.induce P).induce {z | z ≠ x}).Preconnected) :
    ∃ L R : Set V, L.Nonempty ∧ R.Nonempty ∧ Disjoint L R ∧
      L∪R=P\{x.val} ∧ H.IsClique L ∧ H.IsClique R ∧
      (∀l∈L,∀r∈R,¬H.Adj l r) ∧
      (∃l∈L,H.Adj x.val l) ∧ (∃r∈R,H.Adj x.val r) := by
  obtain ⟨A,B,⟨a,ha⟩,⟨b,hb⟩,dis,cover,ca,cb,sep,⟨l,hl,xl⟩,⟨r,hr,xr⟩⟩ :=
    split_cut_into_two_cliques (H.induce P) conn small x cut
  have image_cl (T : Set P) (cl : (H.induce P).IsClique T) :
      H.IsClique (Subtype.val '' T) := by
    rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ diff
    exact cl hu hv (fun eq => diff (congrArg Subtype.val eq))
  refine ⟨Subtype.val '' A,Subtype.val '' B,⟨a.val,a,ha,rfl⟩,⟨b.val,b,hb,rfl⟩,
    Set.disjoint_image_of_injective Subtype.val_injective dis,?_,image_cl A ca,image_cl B cb,?_,
    ⟨l.val,⟨l,hl,rfl⟩,xl⟩,⟨r.val,⟨r,hr,rfl⟩,xr⟩⟩
  · rw [←Set.image_union,cover]
    ext v
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.property,fun h => hz (Subtype.ext (Set.mem_singleton_iff.mp h))⟩
    · rintro ⟨hv,ne⟩
      exact ⟨⟨v,hv⟩,fun eq => ne (Set.mem_singleton_iff.mpr (congrArg Subtype.val eq)),rfl⟩
  · rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩
    exact sep u hu v hv

/-- An actual crossing cannot terminate at the root of an ordinary block;
therefore its odd block has at least three vertices. -/
theorem crossing_companion_big (H : SimpleGraph V) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H) (w u : V) (hw : w∉N.verts) (hu : u∉N.verts)
    (ne : w≠u) (x : ↥(mateBlock H N w ∪ zeroMateRegion H N)) (y : mateBlock H N u)
    (edge : H.Adj x.val y.val) : 3≤(mateBlock H N u).ncard := by
  have diff : u≠y.val := by
    intro eq
    have xu : H.Adj x.val u := eq.symm ▸ edge
    rcases x.property with ht|⟨_,_,away,_⟩
    · exact mateBlock_separated H N hm max hw x.val ht u
        ⟨hu,fun h => ne (Set.mem_singleton_iff.mp h).symm⟩ xu
    · exact away u hu xu
  have two := (Set.one_lt_ncard_iff (Set.toFinite _)).mpr
    ⟨u,y.val,mateBlock_self H N u,y.property,diff⟩
  have parity := Nat.odd_iff.mp (mateBlock_odd H N hm u hu)
  omega

#print axioms labelled_cut_sides
#print axioms crossing_companion_big
end JSP452Audit.StarHost
