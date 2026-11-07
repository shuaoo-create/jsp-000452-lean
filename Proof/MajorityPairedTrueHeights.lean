import MajorityEndpointPartition
namespace JSP452Audit.StarHost

theorem majority_pair_fold (D b c p h ρ d : ℕ) (C Q : ℕ→ℕ) (tot : b+c=D) (lo : 2≤c) (mid : c+1≤b)
    (chosen : p<c-1)
    (exception : 2*C 2+2*C (p+3)+2*C (b+1)+2*C (b+2+p)+2*h+2*d≤
      Q 2+Q (p+3)+Q (b+1)+Q (b+2+p)+D*ρ)
    (pair : ∀z,z<c-1 → z≠p → 2*C (z+3)+2*C (b+2+z)≤Q (z+3)+Q (b+2+z))
    (other : ∀z,z<b-c-1 → 2*C (c+2+z)≤Q (c+2+z)) :
    2*(∑z∈Finset.range (D-1),C (z+2))+2*h+2*d≤(∑z∈Finset.range (D-1),Q (z+2))+D*ρ := by
  classical
  let I := Finset.range (c-1)
  have mem : p∈I := Finset.mem_range.mpr chosen
  have P := Finset.sum_le_sum (s:=I.erase p) (fun z hz => pair z (Finset.mem_range.mp (Finset.mem_erase.mp hz).2)
    (Finset.mem_erase.mp hz).1)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at P
  have M := Finset.sum_le_sum (s:=Finset.range (b-c-1)) (fun z hz => other z (Finset.mem_range.mp hz))
  rw [←Finset.mul_sum] at M
  have drop (F:ℕ→ℕ) (k:ℕ) : (∑z∈I,F (k+z))=(∑z∈I.erase p,F (k+z))+F (k+p) :=
    (Finset.sum_erase_add I (fun z => F (k+z)) mem).symm
  rw [majority_profile_partition D b c tot lo mid C,majority_profile_partition D b c tot lo mid Q]
  change 2*(C 2+(∑z∈I,C (z+3))+(∑z∈Finset.range (b-c-1),C (c+2+z))+C (b+1)+∑z∈I,C (b+2+z))+2*h+2*d≤
    Q 2+(∑z∈I,Q (z+3))+(∑z∈Finset.range (b-c-1),Q (c+2+z))+Q (b+1)+(∑z∈I,Q (b+2+z))+D*ρ
  have drop' (F:ℕ→ℕ) : (∑z∈I,F (z+3))=(∑z∈I.erase p,F (z+3))+F (p+3) :=
    (Finset.sum_erase_add I (fun z => F (z+3)) mem).symm
  rw [drop' C,drop' Q,drop C (b+2),drop Q (b+2)]
  omega

#print axioms majority_pair_fold
end JSP452Audit.StarHost