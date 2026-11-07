import PhysicalNinePortSubsetMenu
import TwoConsecutiveExteriorStages
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def portMenuGap (z : Fin 2→ℕ) : ℕ :=
  max (min (z 0) (z 1)) (max (z 0) (z 1)-min (z 0) (z 1))

theorem port_menu_of_gap (z : Fin 2→ℕ) (r : ℕ) (fit : portMenuGap z≤r+1) :
    SplitCapacities z r := by
  classical
  let a := min (z 0) (z 1)
  let b := max (z 0) (z 1)
  have ab : a+b=z 0+z 1 := by dsimp [a,b];omega
  have boundA : a≤r+1 := (Nat.le_max_left _ _).trans fit
  have gap : b-a≤r+1 := (Nat.le_max_right _ _).trans fit
  have boxA : ∃T : Finset (Fin 2),(∑u∈T,z u)=a := by
    by_cases lo:z 0≤z 1
    · exact ⟨{0},by simp [a,min_eq_left lo]⟩
    · exact ⟨{1},by simp [a,min_eq_right (by omega : z 1≤z 0)]⟩
  obtain ⟨A,costA⟩ := boxA
  have costB := Finset.sum_add_sum_compl A z
  rw [Fin.sum_univ_two,costA] at costB
  intro i j total
  rw [Fin.sum_univ_two] at total
  by_cases small : i<a
  · exact ⟨∅,by simp,by simpa [Fin.sum_univ_two] using (show z 0+z 1≤j by omega)⟩
  by_cases mid : i<b
  · exact ⟨A,by omega,by omega⟩
  by_cases both : i<a+b
  · exact ⟨Aᶜ,by omega,by simp only [compl_compl,costA];omega⟩
  exact ⟨Finset.univ,by rw [Fin.sum_univ_two];omega,by simp⟩

/-- The very first nine-degree stage is strictly too short to cover the
actual gap in the four capacity choices. If the eight-degree stage reaches
that gap it has to pay for at least 9+e-h degree losses. -/
theorem strict_nine_port_stage_gap (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (B : Set F.X) (stage : CompleteDegreeStage R.erased 9 B)
    (C : Set ↥(Bᶜ : Set F.X)) (next : CompleteDegreeStage (R.erased.induce Bᶜ) 8 C) :
    let k := portMenuGap R.capacity-(F.r+1)
    B.ncard<k ∧ (k≤B.ncard+C.ncard →
      B.ncard+9+R.portCount≤k+highestWidth F.n F.m F.r) := by
  intro k
  have small : portMenuGap R.capacity≤F.r+k+1 := by dsimp [k];omega
  have menu := port_menu_of_gap R.capacity (F.r+k) small
  have narrow := (strict_nine_original_peak F paid nine).2.1
  have first : B.ncard<k := by
    by_contra! fit
    obtain ⟨V,_,card,fee⟩ := subset_of_stage_price R.erased 9 B stage k fit
    have price := strict_nine_adapted_menu_price F paid nine R V (by rwa [card])
    rw [card] at price
    omega
  refine ⟨first,?_⟩
  intro fit
  obtain ⟨V,card,fee⟩ := two_stage_exact_prefix R.erased 8 B stage C next k fit
  have price := strict_nine_adapted_menu_price F paid nine R V (by rwa [card])
  rw [card] at price
  rw [min_eq_right (Nat.le_of_lt first)] at fee
  omega

#print axioms port_menu_of_gap
#print axioms strict_nine_port_stage_gap
end JSP452Audit.StarHost
