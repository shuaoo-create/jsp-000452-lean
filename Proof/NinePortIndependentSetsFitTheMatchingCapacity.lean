import SeedBothNineDegreeInternalPortTips
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem one_box_boundary (i : Fin 2) : crossCount G (R.box i) (R.box i)ᶜ=1 := by
  let c := (R.select i).val
  have edge := actual_cut_piece_boundary_to_roots G R.K.S R.K.T R.K.apart c.val
  change crossCount G (R.box i) (R.box i)ᶜ=R.K.sPorts c+R.K.tPorts c at edge
  have one := (R.select i).property
  change c∈R.K.onePortBlocks at one
  simpa only [one.1,one.2,Nat.add_zero] using edge

theorem independent_inside_one_box (cap : ∀x,Nat.card (G.neighborSet x)≤9) (i : Fin 2) (I : Set X)
    (sub : I⊆R.box i) (ind : G.IsIndepSet I) : I.ncard≤R.capacity i := by
  let U := R.box i
  let V := U\I
  have dis : Disjoint I V := Set.disjoint_left.mpr (fun _ hi hv => hv.2 hi)
  have ci : Disjoint I Uᶜ := disjoint_compl_right.mono_left sub
  have cv : Disjoint V Uᶜ := disjoint_compl_right.mono_left Set.sdiff_subset
  have iv : I∪V=U := by
    ext x
    exact ⟨fun h => h.elim (fun hx => sub hx) (fun hx => hx.1),
      fun h => by by_cases hx:x∈I;exact Or.inl hx;exact Or.inr ⟨h,hx⟩⟩
  have cover : I∪V∪Uᶜ=Set.univ := by rw [iv,Set.union_compl_self]
  have first := partition_handshake G I V Uᶜ dis ci cv cover
  have second := partition_handshake G V I Uᶜ dis.symm cv ci (by rwa [Set.union_comm V I])
  have full (x) (hx : x∈I) := uniform_tight_piece_full G 3 6 cap R.K.S R.K.T
    (R.select i).val.val (R.select i).val.property x (sub hx)
  have no : G.induce I=⊥ := by
    ext x y;exact ⟨fun e => ind x.property y.property (G.ne_of_adj e) e,False.elim⟩
  rw [degree_sum_full G I 9 full,no,SimpleGraph.edgeSet_bot,Set.ncard_empty] at first
  rw [crossCount_swap G V I] at second
  have upper := degree_sum_le_cap G V 9 (fun x _ => cap x)
  have outer := cross_count_mono G sub (Set.Subset.rfl : Uᶜ⊆Uᶜ)
  rw [R.one_box_boundary i] at outer
  have size := Set.ncard_sdiff_add_ncard_of_subset sub
  have odd := (R.inner i).1
  change V.ncard+I.ncard=U.ncard at size
  change U.ncard=2*R.capacity i+1 at odd
  omega

theorem independent_inside_both_boxes (cap : ∀x,Nat.card (G.neighborSet x)≤9) (I : Set X)
    (sub : I⊆R.chosen) (ind : G.IsIndepSet I) : I.ncard≤R.totalCapacity := by
  let A := I∩R.box 0
  let B := I∩R.box 1
  have split : A∪B=I := by
    ext x
    exact ⟨fun h => h.elim And.left And.left,
      fun h => (sub h).elim (fun zero => Or.inl ⟨h,zero⟩) (fun one => Or.inr ⟨h,one⟩)⟩
  have xa : A⊆R.box 0 := Set.inter_subset_right
  have xb : B⊆R.box 1 := Set.inter_subset_right
  have ra := R.independent_inside_one_box cap 0 A xa (fun {_} hx {_} hy ne => ind hx.1 hy.1 ne)
  have rb := R.independent_inside_one_box cap 1 B xb (fun {_} hx {_} hy ne => ind hx.1 hy.1 ne)
  have total := Set.ncard_union_eq (R.disjoint_boxes.mono xa xb)
  rw [split] at total
  change I.ncard≤R.capacity 0+R.capacity 1
  omega

#print axioms one_box_boundary
#print axioms independent_inside_one_box
#print axioms independent_inside_both_boxes
end JSP452Audit.StarHost.NinePortRegion
