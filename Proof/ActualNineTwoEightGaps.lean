import OnlyTheTwoEightNinthColumnCanRemain
import LastThreeRawPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_last_boundary_gap_kind (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (aligned : (highestWidth F.n F.m F.r:ℤ)≤R.K.eta)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity)
    (j : ℕ) (lo : 2≤j) (hi : j≤9) (gap : R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j) :
    WinsHeight F.n F.m F.r j 2 (j-1) ∧ (j=2 ∨ j=3 ∨ j=9) := by
  have boundary := strict_nine_single_short_only_two_eight F paid nine R aligned long short
  have top : diagonal F.n F.m (F.r+2)=9+1 := by omega
  obtain ⟨_,narrow,_,_,i,k,_,_,_,heads,_⟩ := strict_nine_original_peak F paid nine
  have red3 : 0<originalThresholdCount F.n 3 :=
    Nat.zero_lt_of_lt ((original_threshold_prefix F.n F.hn 3 i).mp (by omega))
  have sep : F.t+F.r+highestWidth F.n F.m F.r<F.s := by
    rcases strict_nine_exactly_one_short_list F paid nine R with h|h <;> omega
  have active : 0<widthAt F.n F.m F.r j := by omega
  obtain ⟨x,y,px,py,h,nx,my,rect⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by omega : 0<j) active
  have win : WinsHeight F.n F.m F.r j x y := ⟨px,py,h,nx,my,rect⟩
  by_cases endAt : j=9
  · rw [endAt]
    exact ⟨boundary.2.1,Or.inr (Or.inr rfl)⟩
  rcases strict_nine_single_short_unpaid_kinds F paid nine R long short j x y gap win with pure|mixed
  · obtain ⟨ey,ex⟩ := pure
    subst y;subst x
    have low : j=2 := by
      by_contra ne
      exact no_pure_axis_at_last_boundary F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.live top
        boundary.1 red3 sep j (by omega) (by omega) win
    subst j;exact ⟨win,Or.inl rfl⟩
  · obtain ⟨ex,_,low|last⟩ := mixed
    · obtain ⟨ey,ej⟩ := low
      subst x;subst y;subst j
      exact ⟨win,Or.inr (Or.inl rfl)⟩
    · have eq := boundary.1
      omega

theorem strict_nine_final_few_nonunits (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (aligned : (highestWidth F.n F.m F.r:ℤ)≤R.K.eta)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity) :
    originalThresholdCount F.n 2≤R.totalCapacity := by
  obtain ⟨j,lo,hi,gap,_,lost⟩ := strict_nine_single_short_missing_column F paid nine R long
  have shape := strict_nine_last_boundary_gap_kind F paid nine R aligned long short j lo hi gap
  exact (lost 2 (j-1) shape.1).2.2.1

#print axioms strict_nine_last_boundary_gap_kind
#print axioms strict_nine_final_few_nonunits
end JSP452Audit.StarHost
