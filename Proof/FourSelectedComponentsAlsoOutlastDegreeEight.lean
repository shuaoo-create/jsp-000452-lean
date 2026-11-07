import PhysicalRowsWhenTheConservativeVolumeFits
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_two_exposures_from_head_cap (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (red:∀i,F.n i≤8) (blue:∀j,F.m j≤8) (H:ThreeDegreeStages (F.G.induce A.K.supportᶜ) 8) :
    let h := highestWidth F.n F.m F.r
    let O := F.G.induce A.K.supportᶜ
    minimumExposure (O.induce H.upperᶜ) 9≤(38+2*h)/7 ∧
      minimumExposure (O.induce H.midCutᶜ) 8≤max 4 ((h-1+((38+2*h)/7-2)+16)/3) := by
  intro h O
  have second := strict_ten_second_exterior_exposure F paid ten A.K.support A.K.support_closed red blue H
  obtain ⟨I,stage,_⟩ := A.shortStage
  obtain ⟨joined,_⟩ := join_closed_degree_stages F.G A.K.support 10 A.K.support_closed I H.upper stage H.first
  have first := (strict_ten_complete_stage F paid ten _ joined).2.2.2.2.2
  rw [exposure_after_closed_stage_split F.G A.K.support A.K.support_closed I H.upper 9] at first
  change 7*(_+minimumExposure (O.induce H.upperᶜ) 9)≤38+2*h at first
  exact ⟨by omega,second⟩

theorem width_six_penultimate_is_paid (P eps h A B M N b c L J:ℕ)
    (six:h=6) (large:21≤P) (pair:eps=2) (first:A≤(38+2*h)/7) (second:B≤max 4 ((h-1+((38+2*h)/7-2)+16)/3))
    (slots:3*M≤2*P+eps) (slots':4*N≤2*P+eps) (top:J-b≤N+max (h-1) (A-2)) (near:L≤P ∨ L-c≤M+B) :
    L+J+h<2*P+5*eps+1+b+c := by subst h;subst eps;rcases near with _|_ <;> omega

theorem width_six_cannot_finish_at_eight (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (six:highestWidth F.n F.m F.r=6) (eps:A.K.eps=2) (large:21≤A.K.P) (slack:1≤A.K.slack) (H:ThreeDegreeStages (F.G.induce A.K.supportᶜ) 8) :
    H.lastCut.ncard<A.steps := by
  let h := highestWidth F.n F.m F.r
  let O := F.G.induce A.K.supportᶜ
  have e := A.K.positive
  have volume := width_six_conservative_capacity F paid ten A six eps slack
  obtain ⟨red,blue⟩ := width_six_regular_lists_at_most_eight F paid ten A six eps
  have orig (x:↥(A.K.supportᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  have cap := H.degree_caps orig
  have top := ten_tenth_column_on_first_cut F paid ten A.K H.upper cap.1 3 (by decide)
    (fun i => by have := red i;omega) (fun i => by have := blue i;omega)
  have near := ten_ninth_column_on_second_cut F A.K red blue H.midCut cap.2.1
  obtain ⟨one,two⟩ := ten_two_exposures_from_head_cap F paid ten A red blue H
  have bound := width_six_penultimate_is_paid A.K.P A.K.eps h
    (minimumExposure (O.induce H.upperᶜ) 9) (minimumExposure (O.induce H.midCutᶜ) 8)
    (chosenSlots F.G A.K.selected 2) (chosenSlots F.G A.K.selected 3) H.upper.ncard H.midCut.ncard
    (widthAt F.n F.m F.r 9) (widthAt F.n F.m F.r 10)
    six large eps one two
    (ten_regular_slot_volume A.K 2) (ten_regular_slot_volume A.K 3) top near
  by_contra! fits
  obtain ⟨_,_,_,_,_,_,_,fee⟩ := A.real_penultimate_when_capacity_fits paid ten volume H fits
  change _≤widthAt F.n F.m F.r 9+widthAt F.n F.m F.r 10+h at fee
  omega


theorem width_six_regular_heads_at_most_seven (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F)
    (six:highestWidth F.n F.m F.r=6) (order:A.K.eps=2) (large:21≤A.K.P) (slack:1≤A.K.slack) : (∀i,F.n i≤7) ∧ (∀j,F.m j≤7) := by
  have eps := A.K.positive
  have volume := width_six_conservative_capacity F paid ten A six order slack
  obtain ⟨H⟩ := three_degree_stages_exist (F.G.induce A.K.supportᶜ) 8
  have short := width_six_cannot_finish_at_eight F paid ten A six order large slack H
  have present := (A.prefix_when_capacity_fits paid ten volume H).2
  constructor
  · intro i;by_contra! high
    have live := (original_threshold_prefix F.n F.hn 8 i).mp high
    exact short.not_ge (present (Or.inl (by omega)))
  · intro j;by_contra! high
    have live := (original_threshold_prefix F.m F.hm 8 j).mp high
    exact short.not_ge (present (Or.inr (by omega)))

#print axioms ten_two_exposures_from_head_cap
#print axioms width_six_penultimate_is_paid
#print axioms width_six_cannot_finish_at_eight
#print axioms width_six_regular_heads_at_most_seven
end JSP452Audit.StarHost
