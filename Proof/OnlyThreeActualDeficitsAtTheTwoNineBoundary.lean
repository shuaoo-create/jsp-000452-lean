import OnlyTheTwoNineTenthColumnCanRemain
import LastThreeRawPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_last_boundary_gap_kind (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (excess:highestWidth F.n F.m F.r+2+R.epsilon≤R.eta)
    (balanced:R.eta≤F.rank-matchingEdges F.G+1)
    (long : R.capacity<F.s) (short : F.t≤R.capacity)
    (j : ℕ) (lo : 2≤j) (hi : j≤10) (gap : R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j) :
    WinsHeight F.n F.m F.r j 2 (j-1) ∧ (j=2 ∨ j=3 ∨ j=10) := by
  have boundary := ten_single_short_only_two_nine F paid ten R small excess balanced long short
  have top : diagonal F.n F.m (F.r+2)=10+1 := by omega
  obtain ⟨i,k,_,_,_,_,heads,_⟩ := strict_ten_true_factor_peak F paid ten
  have red3 : 0<originalThresholdCount F.n 3 :=
    Nat.zero_lt_of_lt ((original_threshold_prefix F.n F.hn 3 i).mp (by omega))
  have sep : F.t+F.r+highestWidth F.n F.m F.r<F.s := by
    have guard := (ten_long_side_exterior_endpoints F paid ten R small (by omega) long).1
    omega
  have active : 0<widthAt F.n F.m F.r j := by omega
  obtain ⟨x,y,px,py,h,nx,my,rect⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by omega : 0<j) active
  have win : WinsHeight F.n F.m F.r j x y := ⟨px,py,h,nx,my,rect⟩
  by_cases endAt : j=10
  · rw [endAt]
    exact ⟨boundary.2.1,Or.inr (Or.inr rfl)⟩
  rcases ten_single_short_unpaid_kinds F paid ten R small (by omega) balanced long short j x y gap win with pure|mixed
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

theorem ten_final_few_nonunits (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (excess:highestWidth F.n F.m F.r+2+R.epsilon≤R.eta)
    (balanced:R.eta≤F.rank-matchingEdges F.G+1)
    (long : R.capacity<F.s) (short : F.t≤R.capacity) :
    originalThresholdCount F.n 2≤R.capacity := by
  obtain ⟨j,lo,hi,gap,_,lost⟩ := ten_actual_missing_threshold F paid ten R small excess long
  have shape := ten_last_boundary_gap_kind F paid ten R small excess balanced long short j lo hi gap
  exact (lost 2 (j-1) shape.1).2.2.1

#print axioms ten_last_boundary_gap_kind
#print axioms ten_final_few_nonunits
end JSP452Audit.StarHost
