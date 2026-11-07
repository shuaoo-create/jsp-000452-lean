import AverageTheSelectedVerticesAndTheUndominatedFullDegreeVerticesTogether
open private JSP452Audit.StarHost.handshake_cap from PositiveCoreCaps
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem fifth_tail_large_degree (D:ℕ) (large:11≤D) : ((D:ℚ)-3)*(4/5:ℚ)^(D+1)≤3/5 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le large
  induction k with
  | zero => norm_num
  | succ k step =>
    have next : (11+(k+1))+1=(11+k+1)+1 := by omega
    rw [next,pow_succ]
    push_cast at step ⊢
    have dec : 0≤((11:ℚ)+k-3)-((11:ℚ)+(k+1)-3)*(4/5) := by linarith only [show (0:ℚ)≤k by positivity]
    have gain := mul_nonneg dec (show (0:ℚ)≤(4/5:ℚ)^(11+k+1) by positivity)
    linarith only [gain,step (by omega)]

theorem choose_one_weighted_fifth {V:Type u} [Finite V] (C:SimpleGraph V) (D Z:ℕ)
    (degree:11≤D) (cap:∀v,Nat.card (C.neighborSet v)≤D)
    (order:D*Nat.card V≤(2*D+2)*Z) :
    ∃f:V→Fin 5,3*(D-1)*(fifthChosen f).ncard+(D-3)*(fifthUndominated C D f).ncard+
      2*(C.induce (fifthChosen f)ᶜ).edgeSet.ncard≤3*(D-1)*Z := by
  classical
  let _ := Fintype.ofFinite V
  let L := V→Fin 5
  let N := Nat.card V
  let den := (5:ℚ)^N
  let score (f:L) := 3*(D-1)*(fifthChosen f).ncard+(D-3)*(fifthUndominated C D f).ncard+
    2*(C.induce (fifthChosen f)ᶜ).edgeSet.ncard
  have chosen := fifth_selected_total (V:=V)
  have missing := fifth_undominated_total C D
  have darts := fifth_surviving_darts_total C
  change (∑f:L,((fifthChosen f).ncard:ℚ))=den*((N:ℚ)/5) at chosen
  change (∑f:L,((fifthUndominated C D f).ncard:ℚ))≤den*N*(4/5:ℚ)^(D+1) at missing
  change (∑f:L,((2*(C.induce (fifthChosen f)ᶜ).edgeSet.ncard:ℕ):ℚ))=den*(16/25)*(2*C.edgeSet.ncard) at darts
  have handshake := JSP452Audit.StarHost.handshake_cap C D cap
  have edges : (2:ℚ)*C.edgeSet.ncard≤(N:ℚ)*D := by exact_mod_cast handshake
  have size : (D:ℚ)*N≤(2*(D:ℚ)+2)*Z := by exact_mod_cast order
  have dn : 0<den := by dsimp only [den];positivity
  have dQ : (11:ℚ)≤D := by exact_mod_cast degree
  have cd : 0≤(D:ℚ)-3 := by linarith only [dQ]
  have mean : (∑f:L,(score f:ℚ))≤den*(3*((D:ℚ)-1)*Z) := by
    have one : ((D-1:ℕ):ℚ)=(D:ℚ)-1 := by rw [Nat.cast_sub (by omega),Nat.cast_one]
    have three : ((D-3:ℕ):ℚ)=(D:ℚ)-3 := by rw [Nat.cast_sub (by omega)];norm_num
    have expr (f:L) : (score f:ℚ)=3*((D:ℚ)-1)*(fifthChosen f).ncard+((D:ℚ)-3)*(fifthUndominated C D f).ncard+((2*(C.induce (fifthChosen f)ᶜ).edgeSet.ncard:ℕ):ℚ) := by
      dsimp only [score];push_cast;rw [one,three]
    rw [Finset.sum_congr rfl (fun f _ => expr f),Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,chosen,darts]
    have M := mul_le_mul_of_nonneg_left missing cd
    have discount := mul_le_mul_of_nonneg_left (fifth_tail_large_degree D degree) (show (0:ℚ)≤den*N by positivity)
    have edgeBill := mul_le_mul_of_nonneg_left edges (show (0:ℚ)≤den*(16/25) by positivity)
    have orderBill := mul_le_mul_of_nonneg_left size dn.le
    have margin := mul_nonneg (show (0:ℚ)≤13*(D:ℚ)-137 by linarith only [dQ])
      (show (0:ℚ)≤den*Z by positivity)
    linarith only [M,discount,edgeBill,orderBill,margin]
  have card : (Fintype.card L:ℚ)=den := by
    rw [←Nat.card_eq_fintype_card];change (Nat.card (V→Fin 5):ℚ)=(5:ℚ)^N
    rw [Nat.card_fun,Nat.card_fin];push_cast;rfl
  by_contra! none
  have strict (f:L) : 3*((D:ℚ)-1)*Z<(score f:ℚ) := by
    have quote : ((3*(D-1)*Z:ℕ):ℚ)<(score f:ℚ) := by exact_mod_cast none f
    simpa [Nat.cast_sub (show 1≤D by omega)] using quote
  have less := Finset.sum_lt_sum (s:=Finset.univ) (fun f _ => (strict f).le) ⟨(fun _ => 0:L),Finset.mem_univ _,strict _⟩
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card] at less
  linarith only [less,mean]

#print axioms fifth_tail_large_degree
#print axioms choose_one_weighted_fifth
end JSP452Audit.StarHost