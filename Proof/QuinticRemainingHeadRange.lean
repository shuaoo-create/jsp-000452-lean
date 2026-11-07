import StrictQuinticBinaryExcluded
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_quintic_heads_and_positive_offset (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (five : diagonal F.n F.m (F.r+2)-1=5) :
    0<F.r ∧ ((F.n ⟨0,F.hs⟩=5 ∧ (F.m ⟨0,F.ht⟩=3 ∨ F.m ⟨0,F.ht⟩=4)) ∨
      (F.m ⟨0,F.ht⟩=5 ∧ (F.n ⟨0,F.hs⟩=3 ∨ F.n ⟨0,F.hs⟩=4))) := by
  let D := diagonal F.n F.m (F.r+2)-1
  obtain ⟨K⟩ := degreeRegion_exists F.G D
  have one := strict_full_head_unique_escape F paid K
  have mixed := strict_full_mixed_boundary F paid K
  have binary := strict_quintic_binary_excluded F paid five
  have cases : (F.n ⟨0,F.hs⟩=5 ∧ (F.m ⟨0,F.ht⟩=3 ∨ F.m ⟨0,F.ht⟩=4)) ∨
      (F.m ⟨0,F.ht⟩=5 ∧ (F.n ⟨0,F.hs⟩=3 ∨ F.n ⟨0,F.hs⟩=4)) := by
    rcases five_degree_requires_original_full_head F paid five with red|blue
    · have cap := (one.1 (red.trans five.symm)).2.2.2 ⟨0,F.ht⟩
      obtain ⟨_,y,lo,_,_,present,_,_,_⟩ := mixed.1 (red.trans five.symm)
      have hi := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 present
      exact Or.inl ⟨red,by omega⟩
    · have cap := (one.2 (blue.trans five.symm)).2.2.2 ⟨0,F.hs⟩
      obtain ⟨_,y,lo,_,_,present,_,_,_⟩ := mixed.2 (blue.trans five.symm)
      have hi := (original_threshold_prefix F.n F.hn y ⟨0,F.hs⟩).2 present
      exact Or.inr ⟨blue,by omega⟩
  refine ⟨?_,cases⟩
  by_contra! bad
  have zero : F.r=0 := by omega
  rw [zero] at five
  have first := antiDiag_member F.n F.m ⟨0,F.hs⟩ ⟨0,F.ht⟩
  change F.n ⟨0,F.hs⟩+F.m ⟨0,F.ht⟩-1≤diagonal F.n F.m (0+2) at first
  rcases cases with h|h <;> omega

#print axioms strict_quintic_heads_and_positive_offset
end JSP452Audit.StarHost