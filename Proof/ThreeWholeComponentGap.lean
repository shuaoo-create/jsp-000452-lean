import SixLowWidthOnlyOneComponent
namespace JSP452Audit.StarHost

theorem extend_capacity_splits {n:ℕ} (z:Fin (n+1)→ℕ) (r:ℕ)
    (tail:SplitCapacities (fun i:Fin n => z i.succ) r)
    (bridge:z 0≤r+(∑i:Fin n,z i.succ)+1) : SplitCapacities z r := by
  classical
  intro i j total
  rw [Fin.sum_univ_succ] at total
  let lift (T:Finset (Fin n)) := T.map (Fin.succEmb _)
  have sumLift (T:Finset (Fin n)) : (∑v∈lift T,z v)=∑v∈T,z v.succ := Finset.sum_map _ _ _
  have fresh (T:Finset (Fin n)) : (0:Fin (n+1))∉lift T := by
    intro mem;obtain ⟨v,_,eq⟩ := Finset.mem_map.mp mem;exact Fin.succ_ne_zero v eq
  by_cases fits : z 0≤ i
  · obtain ⟨T,red,blue⟩ := tail (i-z 0) j (by dsimp only;omega)
    dsimp only at red blue
    let V := insert 0 (lift T)
    have value : (∑v∈V,z v)=z 0+∑v∈T,z v.succ := by rw [Finset.sum_insert (fresh T),sumLift]
    have split := Finset.sum_add_sum_compl V z
    have rest := Finset.sum_add_sum_compl T (fun v => z v.succ)
    rw [Fin.sum_univ_succ,value] at split
    exact ⟨V,by rw [value];omega,by omega⟩
  · have fitsB : z 0≤j := by omega
    obtain ⟨T,red,blue⟩ := tail i (j-z 0) (by dsimp only;omega)
    dsimp only at red blue
    let V := lift T
    have value := sumLift T
    have split := Finset.sum_add_sum_compl V z
    have rest := Finset.sum_add_sum_compl T (fun v => z v.succ)
    change (∑v∈V,z v)=(∑v∈T,z v.succ) at value
    rw [Fin.sum_univ_succ,value] at split
    exact ⟨V,value ▸ red,by omega⟩

theorem three_capacity_splits (z:Fin 3→ℕ) (r:ℕ) (ord:z 1≤z 2) (small:z 1≤r+1)
    (middle:z 2-z 1≤r+1) (large:z 0-(z 1+z 2)≤r+1) : SplitCapacities z r := by
  apply extend_capacity_splits z r (two_capacity_splits (fun i:Fin 2 => z i.succ) r ord small middle)
  rw [Fin.sum_univ_two]
  change z 0≤r+(z 1+z 2)+1
  omega

#print axioms extend_capacity_splits
#print axioms three_capacity_splits
end JSP452Audit.StarHost
