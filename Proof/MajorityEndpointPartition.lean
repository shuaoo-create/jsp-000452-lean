import OriginalFullGapThreeNecessary
namespace JSP452Audit.StarHost

theorem majority_profile_partition (D b c : ℕ) (tot : b+c=D) (lo : 2≤c) (mid : c+1≤b) (F : ℕ→ℕ) :
    (∑z∈Finset.range (D-1),F (z+2))=
      F 2+(∑z∈Finset.range (c-1),F (z+3))+(∑z∈Finset.range (b-c-1),F (c+2+z))+F (b+1)+
      ∑z∈Finset.range (c-1),F (b+2+z) := by
  have lower := Finset.sum_range_add (fun z => F (z+2)) 1 (c-1)
  simp only [Finset.sum_range_one,Nat.zero_add] at lower
  have central := Finset.sum_range_add (fun z => F (z+2)) c (b-c-1)
  have high := Finset.sum_range_add (fun z => F (z+2)) b (c-1)
  have full := Finset.sum_range_succ (fun z => F (z+2)) (b-1)
  rw [show D-1=b+(c-1) by omega,high,show b=(b-1)+1 by omega,full]
  have eqc : c+(b-c-1)=b-1 := by omega
  rw [eqc] at central
  rw [central,show 1+(c-1)=c by omega] at *
  rw [lower]
  have eq1 (z:ℕ) : 1+z+2=z+3 := by omega
  have eq2 (z:ℕ) : c+z+2=c+2+z := by omega
  have eq3 (z:ℕ) : (b-1+1)+z+2=b+2+z := by omega
  simp only [eq1,eq2,eq3,show b-1+2=b+1 by omega,show b-1+1=b by omega]
  simp [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

#print axioms majority_profile_partition
end JSP452Audit.StarHost