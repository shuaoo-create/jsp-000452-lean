import CubicSingleEscapeMixedCorner
import UniformSubforest
namespace JSP452Audit.StarHost
open SimpleGraph

private def leftFlag {X Y : Type*} : X⊕Y → Bool := Sum.elim (fun _ => true) (fun _ => false)

private theorem flag_of_adj {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    {x y : X⊕Y} (adj : (G ⊕g H).Adj x y) : leftFlag x=leftFlag y := by
  cases x <;> cases y
  · rfl
  · exact (not_adj_sum_inl_inr _ _ adj).elim
  · exact (not_adj_sum_inl_inr _ _ adj.symm).elim
  · rfl

private theorem star_coordinate_flag {I X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (n : I→ℕ) (f : (forest n).Copy (G ⊕g H)) (i : I) (j : Fin (n i+1)) :
    leftFlag (f ⟨i,j⟩)=leftFlag (f (center n i)) := by
  refine Fin.cases ?_ (fun b => ?_) j
  · rfl
  · exact (flag_of_adj (f.toHom.map_adj (starEdge n ⟨i,b⟩))).symm

private theorem left_projection {I X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (n : I→ℕ) (f : (forest n).Copy (G ⊕g H)) (U : Set I)
    (inside : ∀i∈U,leftFlag (f (center n i))=true) :
    (forest (fun i : U => n i.val)).IsContained G := by
  classical
  let sub := subforestCopy (fun i : U => n i.val) n (Function.Embedding.subtype _) (fun _ => le_rfl)
  have land (z : Vertices (fun i : U => n i.val)) : ∃x:X,Sum.inl x=f (sub z) := by
    have yes := (star_coordinate_flag n f z.1.val z.2).trans (inside _ z.1.property)
    change leftFlag (f (sub z))=true at yes
    cases eq : f (sub z) with
    | inl x => exact ⟨x,rfl⟩
    | inr y => rw [eq] at yes;contradiction
  let g (z : Vertices (fun i : U => n i.val)) := (land z).choose
  have eq (z : Vertices (fun i : U => n i.val)) : Sum.inl (g z)=f (sub z) := (land z).choose_spec
  refine ⟨{ toHom := {toFun := g,map_rel' := ?_},injective' := ?_}⟩
  · intro a b e
    have edge := f.toHom.map_adj (sub.toHom.map_adj e)
    change (G ⊕g H).Adj (f (sub a)) (f (sub b)) at edge
    rw [←eq a,←eq b] at edge
    exact edge
  · intro a b same
    exact sub.injective (f.injective ((eq a).symm.trans ((congrArg Sum.inl same).trans (eq b))))

/-- A single actual forest copy in a disjoint sum assigns every whole
original star to exactly one side. Both induced sublists retain their labels. -/
theorem split_copy_on_sum {I X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y)
    (n : I→ℕ) (copy : (forest n).IsContained (G ⊕g H)) :
    ∃U:Set I,(forest (fun i:U => n i.val)).IsContained G ∧
      (forest (fun i:↥(Uᶜ : Set I) => n i.val)).IsContained H := by
  obtain ⟨f⟩ := copy
  let U : Set I := {i | leftFlag (f (center n i))=true}
  refine ⟨U,left_projection n f U (fun _ h => h),?_⟩
  let comm : G ⊕g H ≃g H ⊕g G := Iso.sumComm
  let g := comm.toCopy.comp f
  apply left_projection n g Uᶜ
  intro i hi
  change ¬ leftFlag (f (center n i))=true at hi
  change leftFlag (Sum.swap (f (center n i)))=true
  cases eq : f (center n i) with
  | inl x => rw [eq] at hi;exact (hi rfl).elim
  | inr y => rfl

#print axioms split_copy_on_sum
end JSP452Audit.StarHost
