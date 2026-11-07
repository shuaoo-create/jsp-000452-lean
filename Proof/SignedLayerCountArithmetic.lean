import LayerSubsetForcesOriginalLabelCount
namespace JSP452Audit.StarHost

theorem signed_layer_count_bound {r s l:ℕ} (w:Fin (r+s)→ℕ) (positive:0<l) (haveS:0<s)
    (oddCount:(Finset.univ.filter (fun i => Odd (w i))).card≤1)
    (all:∀T:Finset (Fin (r+s)),T.card=s → l≤∑i∈T,w i) :
    l+2*r*((l-1)/(2*s)+1)≤∑i,w i := by
  classical
  let v := (l-1)/(2*s)+1
  let good := Finset.univ.filter (fun i => Even (w i) ∧ 2*v≤w i)
  let small := Finset.univ.filter (fun i => Even (w i) ∧ w i<2*v)
  let odd := Finset.univ.filter (fun i => Odd (w i))
  have partition : good∪small∪odd=Finset.univ := by
    ext i
    by_cases ev:Even (w i)
    · by_cases lo:2*v≤w i <;> simp [good,small,odd,ev,lo,Nat.lt_of_not_ge]
    · have od := Nat.not_even_iff_odd.mp ev
      simp [good,small,odd,od]
  have count := Finset.card_union_le (good∪small) odd
  have first := Finset.card_union_le good small
  rw [partition,Finset.card_univ,Fintype.card_fin] at count
  change odd.card≤1 at oddCount
  have many : r≤good.card := by
    by_contra! few
    have enough : s≤small.card := by omega
    obtain ⟨T,sub,size⟩ := Finset.exists_subset_card_eq enough
    have bound (i) (hi:i∈T) : w i≤2*(v-1) := by
      obtain ⟨⟨j,eq⟩,less⟩ := (Finset.mem_filter.mp (sub hi)).2
      omega
    have total := Finset.sum_le_sum (s:=T) bound
    rw [Finset.sum_const,size,nsmul_eq_mul,Nat.cast_id] at total
    have required := all T size
    have quo := Nat.mul_div_le (l-1) (2*s)
    have paid : s*(2*(v-1))≤l-1 := by
      dsimp [v]
      simpa [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using quo
    omega
  obtain ⟨R,inc,qty⟩ := Finset.exists_subset_card_eq many
  have sum := Finset.sum_le_sum (s:=R) (fun i hi => (Finset.mem_filter.mp (inc hi)).2.2)
  rw [Finset.sum_const,qty,nsmul_eq_mul,Nat.cast_id] at sum
  have left := all Rᶜ (by rw [Finset.card_compl,Fintype.card_fin,qty];omega)
  have total := Finset.sum_add_sum_compl R w
  have scale : r*(2*v)=2*r*v := by ring
  rw [scale] at sum
  change l+2*r*v≤_
  omega

#print axioms signed_layer_count_bound
end JSP452Audit.StarHost
