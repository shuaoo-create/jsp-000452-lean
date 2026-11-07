import CubicEarlyGreedyStep
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Each label is a separate genuine pair, even if several labels have
the same two endpoints. -/
structure CubicPairFamily (X I : Type*) where
  left : I→X
  right : I→X
  distinct : ∀i,left i≠right i

namespace CubicPairFamily
variable {X I : Type*} [Fintype X] [Fintype I] (P : CubicPairFamily X I)

noncomputable def active (U:Set X) : Finset I := by
  classical
  exact Finset.univ.filter (fun i => P.left i∈U ∧ P.right i∈U)

theorem mem_active (U:Set X) (i:I) : i∈P.active U ↔ P.left i∈U ∧ P.right i∈U := by
  classical
  simp [active]

theorem active_mono {T U:Set X} (sub:T⊆U) : P.active T⊆P.active U := by
  intro i hi
  obtain ⟨l,r⟩ := (P.mem_active T i).1 hi
  exact (P.mem_active U i).2 ⟨sub l,sub r⟩

noncomputable def degree (U:Set X) (x:X) : ℕ := by
  classical
  exact ((P.active U).filter (fun i => P.left i=x)).card+
    ((P.active U).filter (fun i => P.right i=x)).card

theorem degree_mono {T U:Set X} (sub:T⊆U) (x:X) : P.degree T x≤P.degree U x := by
  classical
  exact Nat.add_le_add (Finset.card_le_card (Finset.filter_subset_filter _ (P.active_mono sub)))
    (Finset.card_le_card (Finset.filter_subset_filter _ (P.active_mono sub)))

theorem degree_sum (U T:Set X) [DecidablePred (·∈T)] : fourLabelSum T (P.degree U)=
    ((P.active U).filter (fun i => P.left i∈T)).card+((P.active U).filter (fun i => P.right i∈T)).card := by
  classical
  unfold fourLabelSum degree
  rw [Finset.sum_add_distrib]
  have left := Finset.sum_card_fiberwise_eq_card_filter (P.active U) T.toFinset P.left
  have right := Finset.sum_card_fiberwise_eq_card_filter (P.active U) T.toFinset P.right
  simp only [Set.mem_toFinset] at left right
  convert congrArg₂ (fun a b : ℕ => a+b) left right using 2 <;> congr 2 <;> apply Subsingleton.elim

/-- Crossing pairs contribute once and internal pairs twice. In particular,
the formula still counts parallel labelled pairs separately. -/
theorem degree_removal (U T:Set X) (inside:T⊆U) :
    fourLabelSum T (P.degree U)+(P.active (U\T)).card=(P.active U).card+(P.active T).card := by
  classical
  let L := (P.active U).filter (fun i => P.left i∈T)
  let R := (P.active U).filter (fun i => P.right i∈T)
  have meet : L∩R=P.active T := by
    ext i;simp only [L,R,Finset.mem_inter,Finset.mem_filter,mem_active]
    constructor
    · rintro ⟨⟨_,l⟩,_,r⟩;exact ⟨l,r⟩
    · rintro ⟨l,r⟩;exact ⟨⟨⟨inside l,inside r⟩,l⟩,⟨⟨inside l,inside r⟩,r⟩⟩
  have join : L∪R=P.active U\P.active (U\T) := by
    ext i;simp only [L,R,Finset.mem_union,Finset.mem_filter,Finset.mem_sdiff,mem_active,Set.mem_sdiff]
    tauto
  have sub : P.active (U\T)⊆P.active U := P.active_mono Set.sdiff_subset
  have total := Finset.card_union_add_card_inter L R
  rw [meet,join,Finset.card_sdiff_of_subset sub] at total
  rw [P.degree_sum]
  change L.card+R.card+_=_;have bound:=Finset.card_le_card sub;omega

theorem sum_internal (U:Set X) : fourLabelSum U (P.degree U)=2*(P.active U).card := by
  have eq := P.degree_removal U U (Set.Subset.rfl)
  rw [Set.sdiff_self] at eq
  have empty : P.active ∅=∅ := by ext i;simp [mem_active]
  rw [empty,Finset.card_empty,Nat.add_zero] at eq;omega

end CubicPairFamily
#print axioms CubicPairFamily.degree_sum
#print axioms CubicPairFamily.degree_removal
#print axioms CubicPairFamily.sum_internal
end JSP452Audit.StarHost
