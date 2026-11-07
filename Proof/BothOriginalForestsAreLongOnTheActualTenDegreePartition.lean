import ExcludeOneShortSideOnTheTenDegreePartition
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_partition_strong_lengths (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (R:TenBlockPartition F.G) (small:R.epsilon≤2) (excess:highestWidth F.n F.m F.r+2+R.epsilon≤R.eta)
    (balanced:R.eta≤F.rank-matchingEdges F.G+1) :
    R.roots.ncard+R.capacity+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t ∧
      max F.s F.t≤R.outsideRank := by
  rcases (ten_region_guard_and_long_branches F paid ten R small excess).2 with good|left|right
  · exact good
  · let B := F.exchangeSides
    have rank : B.rank=F.rank := by change rowCount F.t F.s F.r=rowCount F.s F.t F.r;simp [rowCount,Nat.add_comm]
    have ten' : diagonal B.n B.m (B.r+2)-1=10 := by
      change diagonal F.m F.n (F.r+2)-1=10
      rw [diagonal_swap F.m F.n];exact ten
    have width : highestWidth B.n B.m B.r=highestWidth F.n F.m F.r := highest_width_colour_swap F.m F.n F.r
    exact (ten_short_oriented_partition_impossible B (rank.symm ▸ paid) ten' R small (width.symm ▸ excess)
      (by rw [rank];exact balanced) (by change R.capacity<F.t;omega) left.1).elim
  · exact (ten_short_oriented_partition_impossible F paid ten R small excess balanced (by omega) right.1).elim

#print axioms ten_partition_strong_lengths
end JSP452Audit.StarHost
