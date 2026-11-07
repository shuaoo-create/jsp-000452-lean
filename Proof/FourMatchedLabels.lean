import FourSelectedLoad
namespace JSP452Audit.StarHost
variable {I Z W : Type*} [Finite I] [Finite Z] [Finite W]

theorem select_four_matched_labels [Nonempty I] [Nonempty Z] (f : Z→I) (A : I→Set W)
    (size : Nat.card Z=4) (degree : ∀i,(ownerFiber f i).ncard+(A i).ncard=4)
    (notAll : ∀i,(ownerFiber f i).ncard<4) (holeDeg : ∀w:W,{j:I|w∈A j}.ncard=4) :
    ∃i z z₀ a b p q, f z=i ∧ z≠z₀ ∧ a≠b ∧ a∈A i ∧ b∈A i ∧
      p≠i ∧ q≠i ∧ p≠q ∧ a∈A p ∧ b∈A q ∧
      ∀j,j≠i → survivingRootLoad f A z₀ a b j≤3 ∧
        (survivingRootLoad f A z₀ a b j=3 → j=p ∨ j=q) := by
  classical
  obtain ⟨i,z,z₀,a,b,own,diff,ab,ai,bi,cap,small⟩ :=
    select_four_deletion_labels f A size degree notAll
  let candidates (w : W) : Set I := {j|w∈A j} \ {i}
  let J := {j | j≠i ∧ survivingRootLoad f A z₀ a b j=3}
  have count (w : W) (wi : w∈A i) : 3≤(candidates w).ncard := by
    have size := Set.ncard_sdiff_singleton_add_one (show i∈{j|w∈A j} from wi)
    rw [holeDeg] at size
    dsimp [candidates];omega
  have left : J⊆candidates a := fun j h => ⟨((cap j h.1).2 h.2).1,fun eq => h.1 eq⟩
  have right : J⊆candidates b := fun j h => ⟨((cap j h.1).2 h.2).2,fun eq => h.1 eq⟩
  obtain ⟨p,hp,q,hq,pq,cover⟩ := allocate_two_hole_mates _ _ J (count a ai) (count b bi) small left right
  refine ⟨i,z,z₀,a,b,p,q,own,diff,ab,ai,bi,fun eq => hp.2 eq,fun eq => hq.2 eq,pq,hp.1,hq.1,?_⟩
  intro j ji
  refine ⟨(cap j ji).1,?_⟩
  intro eq
  exact cover (show j∈J from ⟨ji,eq⟩)

#print axioms select_four_matched_labels
end JSP452Audit.StarHost
