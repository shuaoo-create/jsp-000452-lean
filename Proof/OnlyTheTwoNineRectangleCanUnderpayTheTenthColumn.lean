import PriceOfALargeMixedTenthColumn
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_joint_payment_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (R:TenBlockPartition F.G) (slack:ℕ)
    (covered:slack+2*highestWidth F.n F.m F.r+R.epsilon≤10*R.eta+(F.G.induce R.roots).edgeSet.ncard+
      crossCount F.G R.roots R.rest)
    (funded:2*interiorArea F.n F.m F.r 10+2*(F.rank-matchingEdges F.G)≤
      (∑i∈Finset.range 9,R.jointPrice (i+2))+slack) : False := by
  have contra := ten_joint_envelope_account F paid ten R
  omega

theorem ten_single_short_tenth_unpaid_is_two_nine (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (R:TenBlockPartition F.G) (small:R.epsilon≤2)
    (many:1≤R.eta) (balanced:R.eta≤F.rank-matchingEdges F.G+1) (long:R.capacity<F.s) (short:F.t≤R.capacity)
    (loss:R.basicPrice F.n F.m F.r 10<2*widthAt F.n F.m F.r 10) :
    F.m ⟨0,F.ht⟩=9 ∧ ∀x y,WinsHeight F.n F.m F.r 10 x y → x=2 ∧ y=9 := by
  have bounds := (strict_only_double_escape F paid).1
  have cap := bounds ⟨0,F.hs⟩
  rw [ten] at cap
  have every (x y:ℕ) (win:WinsHeight F.n F.m F.r 10 x y) : x=2 ∧ y=9 ∧ F.m ⟨0,F.ht⟩=9 := by
    rcases ten_single_short_unpaid_kinds F paid ten R small many balanced long short 10 x y loss win with one|two
    · have pos := win.2.2.2.1
      have limit := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 pos
      omega
    · obtain ⟨hx,_,pair|last⟩ := two
      · omega
      · omega
  have positive : 0<widthAt F.n F.m F.r 10 := by omega
  obtain ⟨x,y,p,q,h,n,m,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by decide : 0<10) positive
  exact ⟨(every x y ⟨p,q,h,n,m,w⟩).2.2,fun i j ok => ⟨(every i j ok).1,(every i j ok).2.1⟩⟩

#print axioms ten_joint_payment_impossible
#print axioms ten_single_short_tenth_unpaid_is_two_nine
end JSP452Audit.StarHost
