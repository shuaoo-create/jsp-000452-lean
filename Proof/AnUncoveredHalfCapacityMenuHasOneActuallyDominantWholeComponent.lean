import StoppingAtTheActualHighStageForcesAnUncoveredWholeCapacityInterval
namespace JSP452Audit.StarHost

theorem split_all_but_one_capacity {I:Type*} [Fintype I] [DecidableEq I] (z:I→ℕ) (Q:I) (r:ℕ)
    (small:∀j,j≠Q → z j≤r+1) (bridge:2*z Q≤(∑j,z j)+r+1) : SplitCapacities z r := by
  classical
  let mask (j:I) := if j=Q then 0 else z j
  have erased (T:Finset I) : (∑j∈T.erase Q,z j)=∑j∈T,mask j := by
    have rep : T.erase Q=T.filter (fun j => j≠Q) := by ext j;simp [and_comm]
    rw [rep,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j _
    simp [mask]
  have total := Finset.sum_erase_add (s:=Finset.univ) z (Finset.mem_univ Q)
  rw [erased] at total
  have fill := split_capacities_of_small mask r (fun j => by by_cases eq:j=Q <;> simp [mask,eq,small])
  intro i j ij
  by_cases left:z Q≤ i
  · obtain ⟨T,a,b⟩ := fill (i-z Q) j (by omega)
    let V := insert Q (T.erase Q)
    have sumV : (∑j∈V,z j)=z Q+∑j∈T,mask j := by dsimp only [V];rw [Finset.sum_insert (Finset.notMem_erase _ _),erased]
    have ct := Finset.sum_add_sum_compl T mask
    have cv := Finset.sum_add_sum_compl V z
    rw [sumV] at cv
    exact ⟨V,by rw [sumV];omega,by omega⟩
  · have right : z Q≤j := by omega
    obtain ⟨T,a,b⟩ := fill i (j-z Q) (by omega)
    let V := T.erase Q
    have sumV : (∑j∈V,z j)=∑j∈T,mask j := erased T
    have ct := Finset.sum_add_sum_compl T mask
    have cv := Finset.sum_add_sum_compl V z
    rw [sumV] at cv
    exact ⟨V,sumV ▸ a,by omega⟩

theorem a_failed_half_capacity_menu_has_a_dominant_piece {I:Type*} [Fintype I] [DecidableEq I] (z:I→ℕ) (r:ℕ)
    (half:(∑j,z j)≤2*(r+1)) (fail:¬SplitCapacities z r) :
    ∃Q,(∑j,z j)+(r+1)<2*z Q := by
  classical
  by_contra! no
  have big : ∃Q,r+1<z Q := by
    by_contra! bound
    exact fail (split_capacities_of_small z r bound)
  obtain ⟨Q,large⟩ := big
  apply fail (split_all_but_one_capacity z Q r _ (by have := no Q;omega))
  intro j ne
  have sum := Finset.sum_erase_add (s:=Finset.univ) z (Finset.mem_univ Q)
  have mem : j∈Finset.univ.erase Q := Finset.mem_erase.mpr ⟨ne,Finset.mem_univ _⟩
  have room := Finset.single_le_sum (f:=z) (fun j _ => Nat.zero_le (z j)) mem
  omega

#print axioms split_all_but_one_capacity
#print axioms a_failed_half_capacity_menu_has_a_dominant_piece
end JSP452Audit.StarHost