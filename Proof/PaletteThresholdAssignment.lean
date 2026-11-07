import SevenCliqueFourStarMenu
import Mathlib.Algebra.BigOperators.Fin
namespace JSP452Audit.StarHost
open SimpleGraph

def headTally {I : Type*} [Fintype I] (n:I→ℕ) (y:ℕ) : ℕ :=
  (Finset.univ.filter (fun i => y≤n i)).card

theorem head_tally_antitone {I : Type*} [Fintype I] (n:I→ℕ) {a b:ℕ} (le:a≤b) :
    headTally n b≤headTally n a := Finset.card_le_card (fun _ hi =>
  Finset.mem_filter.mpr ⟨Finset.mem_univ _,le.trans (Finset.mem_filter.mp hi).2⟩)

theorem center_assignment_from_tallies {I J : Type*} [Fintype I] [Fintype J]
    (n:I→ℕ) (f:J→ℕ) (enough:∀i,headTally n (n i)≤headTally f (n i)) :
    ∃e:I ↪ J,∀i,n i≤f (e i) := by
  classical
  let N (i:I) := Finset.univ.filter (fun j:J => n i≤f j)
  have hall (S:Finset I) : S.card≤(S.biUnion N).card := by
    rcases S.eq_empty_or_nonempty with rfl|non
    · simp
    obtain ⟨i,mem,lowest⟩ := S.exists_min_image n non
    have covered : S⊆Finset.univ.filter (fun k:I => n i≤n k) :=
      fun k hk => Finset.mem_filter.mpr ⟨Finset.mem_univ _,lowest k hk⟩
    have reach : N i⊆S.biUnion N := fun j hj => Finset.mem_biUnion.mpr ⟨i,mem,hj⟩
    exact (Finset.card_le_card covered).trans ((enough i).trans (Finset.card_le_card reach))
  obtain ⟨e,inj,inc⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' N).mp hall
  exact ⟨⟨e,inj⟩,fun i => (Finset.mem_filter.mp (inc i)).2⟩

theorem four_count_eq (f:Fin 4→ℕ) (x:ℕ) : headTally f x=fourCount f x := by
  classical
  change (Finset.univ.filter (fun i => x≤f i)).card=_
  have sum : (∑i:Fin 4, if x≤f i then 1 else 0)=fourCount f x := by
    rw [Fin.sum_univ_four];simp only [fourCount,Nat.add_assoc]
  simpa only [Finset.sum_boole, Nat.cast_id] using sum

theorem copy_from_three_thresholds {I : Type*} [Fintype I]
    (n:I→ℕ) (P : SimpleGraph (Vertices sevenStarLeaves)) (a b c:ℕ)
    (first : ∀i,n i≤a) (second : headTally n (b+1)≤1)
    (third : headTally n (c+1)≤2) (length : Fintype.card I≤3)
    (fit : fitsThree (fun i => Nat.card (Colored sevenStarLeaves P i)) a b c) :
    (forest n).IsContained P := by
  classical
  let f := fun i => Nat.card (Colored sevenStarLeaves P i)
  obtain ⟨ca,cb,cc⟩ := fit
  rw [←four_count_eq] at ca cb cc
  obtain ⟨e,size⟩ := center_assignment_from_tallies n f (by
    intro i
    by_cases above : b<n i
    · exact ((head_tally_antitone n above).trans second).trans (ca.trans (head_tally_antitone f (first i)))
    by_cases middle : c<n i
    · exact ((head_tally_antitone n middle).trans third).trans (cb.trans (head_tally_antitone f (by omega)))
    have total : headTally n (n i)≤Fintype.card I := Finset.card_le_univ _
    exact (total.trans length).trans (cc.trans (head_tally_antitone f (by omega))))
  exact contained_of_center_counts n sevenStarLeaves P e size

#print axioms head_tally_antitone
#print axioms center_assignment_from_tallies
#print axioms four_count_eq
#print axioms copy_from_three_thresholds
end JSP452Audit.StarHost
