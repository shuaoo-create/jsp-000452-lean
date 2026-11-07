import SixUnitsOfJointAllowanceWouldCloseTheNineCase
namespace JSP452Audit.StarHost
open SimpleGraph
universe u v

theorem forest_half_orders_fit_vertices {I X : Type*} [Fintype I] [Finite X] (G : SimpleGraph X)
    (n : I→ℕ) (copy : (forest n).IsContained G) : 2*(∑i,(n i+1)/2)≤Nat.card X := by
  obtain ⟨f⟩ := copy
  have used := Nat.card_le_card_of_injective f f.injective
  change Nat.card (Σi:I,Fin (n i+1))≤Nat.card X at used
  rw [Nat.card_sigma] at used
  simp only [Nat.card_fin] at used
  have paid := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => show 2*((n i+1)/2)≤n i+1 by omega)
  rw [←Finset.mul_sum] at paid
  omega

theorem half_orders_fit_two_odd_boxes {I X Y : Type*} [Fintype I] [Finite X] [Finite Y]
    (A : SimpleGraph X) (B : SimpleGraph Y) (a b : ℕ) (first : Nat.card X=2*a+1)
    (second : Nat.card Y=2*b+1) (m : I→ℕ) (copy : (forest m).IsContained (A⊕g B)) :
    (∑i,(m i+1)/2)≤a+b := by
  classical
  obtain ⟨S,left,right⟩ := split_copy_on_sum A B m copy
  have red := forest_half_orders_fit_vertices A _ left
  have blue := forest_half_orders_fit_vertices B _ right
  let cost (i : I) := (m i+1)/2
  have sum : (∑i:↥S,cost i.val)+(∑i:↥(Sᶜ : Set I),cost i.val)=∑i,cost i :=
    Fintype.sum_subtype_add_sum_subtype (fun i => i∈S) cost
  change 2*(∑i:↥S,cost i.val)≤Nat.card X at red
  change 2*(∑i:↥(Sᶜ : Set I),cost i.val)≤Nat.card Y at blue
  change (∑i,cost i)≤_
  omega

namespace NinePortRegion
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

theorem even_cut_on_two_boxes (w : ℕ) (room : w≤R.totalCapacity) :
    ∃U : Set X,U⊆R.chosen ∧ U.ncard=2*w ∧
      ∀{I : Type v} [Fintype I] (m : I→ℕ),(forest m).IsContained (G.induce (R.chosen\U)) →
        (∑i,(m i+1)/2)≤R.totalCapacity-w := by
  classical
  let x := min w (R.capacity 0)
  let y := w-x
  have split : x+y=w := by dsimp [x,y];omega
  have capX : x≤R.capacity 0 := Nat.min_le_right _ _
  have capY : y≤R.capacity 1 := by change w≤R.capacity 0+R.capacity 1 at room;dsimp [y,x];omega
  have z0 := (R.inner 0).1
  have z1 := (R.inner 1).1
  change (R.box 0).ncard=2*R.capacity 0+1 at z0
  change (R.box 1).ncard=2*R.capacity 1+1 at z1
  obtain ⟨A,asub,acard⟩ := Set.exists_subset_card_eq (s:=R.box 0) (show 2*x≤_ by omega)
  obtain ⟨B,bsub,bcard⟩ := Set.exists_subset_card_eq (s:=R.box 1) (show 2*y≤_ by omega)
  let U := A∪B
  let V := R.box 0\A
  let W := R.box 1\B
  have base := R.disjoint_boxes
  have card : U.ncard=2*w := by rw [Set.ncard_union_eq (base.mono asub bsub),acard,bcard];omega
  have union : V∪W=R.chosen\U := by
    ext v
    constructor
    · rintro (h|h)
      · exact ⟨Or.inl h.1,fun ab => ab.elim h.2 (fun b => Set.disjoint_left.mp base h.1 (bsub b))⟩
      · exact ⟨Or.inr h.1,fun ab => ab.elim (fun a => Set.disjoint_left.mp base (asub a) h.1) h.2⟩
    · intro h
      rcases h.1 with zero|one
      · exact Or.inl ⟨zero,fun a => h.2 (Or.inl a)⟩
      · exact Or.inr ⟨one,fun b => h.2 (Or.inr b)⟩
  have apart : Disjoint V W := base.mono Set.sdiff_subset Set.sdiff_subset
  let iso := regionSumIso G (R.chosen\U) V W union apart (fun v vin t tin edge =>
    (R.box_separation 0 vin.1 edge).elim (fun z => Set.disjoint_left.mp base z tin.1)
      (fun h => R.root_outside_box 0 1 (h ▸ tin.1)))
  have s0 := Set.ncard_sdiff_add_ncard_of_subset asub
  have s1 := Set.ncard_sdiff_add_ncard_of_subset bsub
  have vcount : Nat.card V=2*(R.capacity 0-x)+1 := by change (R.box 0\A).ncard=_;omega
  have wcount : Nat.card W=2*(R.capacity 1-y)+1 := by change (R.box 1\B).ncard=_;omega
  refine ⟨U,Set.union_subset (asub.trans Set.subset_union_left) (bsub.trans Set.subset_union_right),card,?_⟩
  intro I inst m copy
  have pair := half_orders_fit_two_odd_boxes (G.induce V) (G.induce W) _ _ vcount wcount m
    (copy.trans ⟨iso.symm.toCopy⟩)
  change (∑i,(m i+1)/2)≤R.capacity 0+R.capacity 1-w
  omega

#print axioms even_cut_on_two_boxes
end NinePortRegion
#print axioms forest_half_orders_fit_vertices
#print axioms half_orders_fit_two_odd_boxes
end JSP452Audit.StarHost
