import OriginalRootIncidence
import ThreePathRootSelection
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Select one real companion vertex, keeping all root labels and both leaves.
The bounded degrees here are degrees into the retained vertex set. -/
theorem select_original_companion_vertex (Q : SimpleGraph X) (I C : Set X) (a b : X)
    (D : ℕ) (six : 6≤D) (ind : Q.IsIndepSet I) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (ne : a≠b) (ac : a∉C) (bc : b∉C) (cn : C.Nonempty) (budget : crossCount Q I C≤D+1) :
    ∃z∈C,∀i∈I,(Q.neighborSet i∩(I∪{a,b}∪(C\{z}))).ncard≤D-1 := by
  classical
  let _ := Fintype.ofFinite I
  let _ : Nonempty C := ⟨⟨cn.choose,cn.choose_spec⟩⟩
  let F (i:I) := {v:C | Q.Adj i.val v.val}
  let A := ({a,b} : Set X)
  let ell (i:I) := (Q.neighborSet i.val∩A).ncard
  have img (i:I) : Subtype.val '' F i=Q.neighborSet i.val∩C := by
    ext v
    constructor
    · rintro ⟨z,hz,rfl⟩; exact ⟨hz,z.property⟩
    · rintro ⟨adj,hv⟩;exact ⟨⟨v,hv⟩,adj,rfl⟩
  have fc (i:I) : (F i).ncard=(Q.neighborSet i.val∩C).ncard :=
    (Set.ncard_image_of_injective _ Subtype.val_injective).symm.trans (congrArg Set.ncard (img i))
  have small (i:I) : ell i≤2 := by
    have u := Set.ncard_le_ncard (s:=Q.neighborSet i.val∩A) (t:=A) Set.inter_subset_right
    exact u.trans (Set.ncard_pair ne).le
  have cap (i:I) : ell i+(F i).ncard≤D := by
    let N := Q.neighborSet i.val
    have apart : Disjoint A C := by
      apply Set.disjoint_left.mpr
      rintro v (l|r) vc
      · exact ac (l ▸ vc)
      · exact bc ((Set.mem_singleton_iff.mp r) ▸ vc)
    have ds : Disjoint (N∩A) (N∩C) := apart.mono Set.inter_subset_right Set.inter_subset_right
    rw [fc]
    change (N∩A).ncard+(N∩C).ncard≤D
    rw [←Set.ncard_union_eq ds,←Set.inter_union_distrib_left]
    exact (Set.ncard_le_ncard Set.inter_subset_left).trans
      ((Nat.card_coe_set_eq N).symm.trans (reg i.val)).le
  have total : (∑i : I,(Q.neighborSet i.val∩C).ncard)≤D+1 := by
    simpa only [crossCount_eq_neighbor_sum] using budget
  have pair (i j:I) (diff:i≠j) : (F i).ncard+(F j).ncard≤D+1 := by
    rw [fc,fc]
    have sub := Finset.sum_le_sum_of_subset_of_nonneg (f:=fun v:I => (Q.neighborSet v.val∩C).ncard)
      (Finset.subset_univ ({i,j} : Finset I)) (by intros;omega)
    simpa [diff] using sub.trans total
  obtain ⟨z,hz⟩ := choose_clique_deletion F ell D six small cap pair
  refine ⟨z.val,z.property,?_⟩
  intro v vi
  let i : I := ⟨v,vi⟩
  let B := Q.neighborSet v∩(C\{z.val})
  have imgDel : Subtype.val '' (F i\{z})=B := by
    ext w
    constructor
    · rintro ⟨t,⟨adj,nt⟩,rfl⟩
      exact ⟨adj,t.property,fun eq => nt (Set.mem_singleton_iff.mpr (Subtype.ext (Set.mem_singleton_iff.mp eq)))⟩
    · rintro ⟨adj,hc,ne⟩
      exact ⟨⟨w,hc⟩,⟨adj,fun h => ne (Set.mem_singleton_iff.mpr (congrArg Subtype.val (Set.mem_singleton_iff.mp h)))⟩,rfl⟩
  have sub : Q.neighborSet v∩(I∪{a,b}∪(C\{z.val})) ⊆ (Q.neighborSet v∩A)∪B := by
    rintro w ⟨adj,(wi|wa)|wc⟩
    · exact (ind vi wi (show Q.Adj v w from adj).ne adj).elim
    · exact Or.inl ⟨adj,wa⟩
    · exact Or.inr ⟨adj,wc⟩
  have bcard : B.ncard=(F i\{z}).ncard := imgDel ▸ Set.ncard_image_of_injective _ Subtype.val_injective
  have upper := (Set.ncard_le_ncard sub).trans (Set.ncard_union_le (Q.neighborSet v∩A) B)
  rw [bcard] at upper
  exact upper.trans (hz i)

#print axioms select_original_companion_vertex
end JSP452Audit.StarHost
