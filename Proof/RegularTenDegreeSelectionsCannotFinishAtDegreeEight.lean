import TheNinthColumnOnTheSecondActualExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_penultimate_prices_do_not_fit (P eps h A B M N b c L J:ℕ)
    (hp:1≤h) (mass:5≤P) (ep:1≤eps) (sm:eps≤2)
    (cases:h=1 ∨ (eps=2 ∧ (h≤2 ∨ (10≤P ∧ h≤5))))
    (first:A≤(38+2*h)/7) (second:B≤max 4 ((h-1+((38+2*h)/7-2)+16)/3))
    (slots:3*M≤2*P+eps) (slots':4*N≤2*P+eps)
    (tenth:J-b≤N+max (h-1) (A-2)) (ninth:L≤P ∨ L-c≤M+B) :
    L+J+h<2*P+5*eps+1+b+c := by
  rcases cases with one|⟨size,two|⟨many,five⟩⟩
  · subst h
    by_cases small:P≤8
    · interval_cases eps <;> interval_cases P <;> rcases ninth with _|_ <;> omega
    · rcases ninth with _|_ <;> omega
  · subst eps
    interval_cases h <;> rcases ninth with _|_ <;> omega
  · subst eps
    interval_cases h <;> rcases ninth with _|_ <;> omega

theorem ten_priced_menu_excludes_eight_exit (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (cases:highestWidth F.n F.m F.r=1 ∨ (A.K.eps=2 ∧ (highestWidth F.n F.m F.r≤2 ∨
      (10≤A.K.P ∧ highestWidth F.n F.m F.r≤5)))) (H:ThreeDegreeStages (F.G.induce A.K.supportᶜ) 8) :
    H.lastCut.ncard<A.steps := by
  let h := highestWidth F.n F.m F.r
  let O := F.G.induce A.K.supportᶜ
  have e := A.K.positive
  have cost : 6*highestWidth F.n F.m F.r≤13*A.K.eps+6 := by omega
  obtain ⟨red,blue⟩ := strict_ten_no_nine_leaf_with_regular_menu F paid ten A cost
  have orig (x:↥(A.K.supportᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  have cap := H.degree_caps orig
  have top := ten_tenth_column_on_first_cut F paid ten A.K H.upper cap.1 3 (by decide)
    (fun i => by have := red i;omega) (fun i => by have := blue i;omega)
  have near := ten_ninth_column_on_second_cut F A.K red blue H.midCut cap.2.1
  obtain ⟨one,two⟩ := ten_both_exterior_exposures F paid ten A cost H
  have bound := ten_penultimate_prices_do_not_fit A.K.P A.K.eps h
    (minimumExposure (O.induce H.upperᶜ) 9) (minimumExposure (O.induce H.midCutᶜ) 8)
    (chosenSlots F.G A.K.selected 2) (chosenSlots F.G A.K.selected 3) H.upper.ncard H.midCut.ncard
    (widthAt F.n F.m F.r 9) (widthAt F.n F.m F.r 10)
    (strict_ten_inventory F paid ten).1 A.K.minimum_order e A.K.small cases one two
    (ten_regular_slot_volume A.K 2) (ten_regular_slot_volume A.K 3) top near
  by_contra! fits
  obtain ⟨_,_,_,_,_,_,_,fee⟩ := A.penultimate_original_successor paid ten cost H fits
  change _≤widthAt F.n F.m F.r 9+widthAt F.n F.m F.r 10+h at fee
  omega

theorem strict_ten_priced_regular_heads_at_most_seven (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (cases:highestWidth F.n F.m F.r=1 ∨ (A.K.eps=2 ∧ (highestWidth F.n F.m F.r≤2 ∨
      (10≤A.K.P ∧ highestWidth F.n F.m F.r≤5)))) : (∀i,F.n i≤7) ∧ (∀j,F.m j≤7) := by
  have eps := A.K.positive
  have cost : 6*highestWidth F.n F.m F.r≤13*A.K.eps+6 := by omega
  obtain ⟨H⟩ := three_degree_stages_exist (F.G.induce A.K.supportᶜ) 8
  have short := ten_priced_menu_excludes_eight_exit F paid ten A cases H
  have present := (A.physical_stage_prefix paid ten cost H).2
  constructor
  · intro i;by_contra! high
    have live := (original_threshold_prefix F.n F.hn 8 i).mp high
    exact short.not_ge (present (Or.inl (by omega)))
  · intro j;by_contra! high
    have live := (original_threshold_prefix F.m F.hm 8 j).mp high
    exact short.not_ge (present (Or.inr (by omega)))
#print axioms ten_penultimate_prices_do_not_fit
#print axioms ten_priced_menu_excludes_eight_exit
#print axioms strict_ten_priced_regular_heads_at_most_seven
end JSP452Audit.StarHost
