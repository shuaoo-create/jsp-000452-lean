import MaximumEvenWeightIsAnActualComponent
namespace JSP452Audit.StarHost

theorem omit_half_cap_largest {I:Type*} [Fintype I] [DecidableEq I] (z:I→ℕ) (p:ℕ)
    (positive:2≤p) (large:p<Fintype.card I) :
    ∃T:Finset I,Tᶜ.card=p ∧ (∀y∈Tᶜ,∀x∈T,z x≤z y) ∧ ∃c∈T,∀x∈T,z x≤z c := by
  let b := p-1
  have bp : b+1=p := by dsimp [b];omega
  have pos : 0<(b:ℤ) := by dsimp [b];omega
  have more : (b:ℤ)+1<(Fintype.card I:ℤ) := by omega
  have fee : (b:ℤ)*((b:ℤ)+1)<∑_i:I,(b:ℤ) := by
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rw [mul_comm (Fintype.card I:ℤ)]
    exact mul_lt_mul_of_pos_left more pos
  obtain ⟨T,_,count,ord,_,c,mem,last⟩ := heavy_piece_selection z (fun _ => (b:ℤ)) b (fun _ => pos)
    (fun _ => le_rfl) fee
  exact ⟨T,count.trans bp,ord,c,mem,last⟩

theorem omitted_even_weight_bound {I:Type*} [Fintype I] (w:I→ℤ) (p:ℕ) (positive:0<p)
    (upper:∀x,w x≤(p:ℤ)) (T:Finset I) (small:T.card≤p) :
    (∑x∈T,w x)≤(p:ℤ)*((p:ℤ)-1)+(({x:I|w x=(p:ℤ)}:Set _).ncard:ℤ) := by
  classical
  let A := {x:I|w x=(p:ℤ)}
  have each (x) : w x≤((p:ℤ)-1)+(if w x=(p:ℤ) then 1 else 0) := by
    have bound := upper x
    split_ifs <;> omega
  have sum := Finset.sum_le_sum (s:=T) (fun x _ => each x)
  rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul] at sum
  have ones : (∑x∈T,if w x=(p:ℤ) then (1:ℤ) else 0)=((T.filter (fun x => w x=(p:ℤ))).card:ℤ) := by simp
  rw [ones] at sum
  have sub : (↑(T.filter (fun x => w x=(p:ℤ))):Set I)⊆A := fun x h => (Finset.mem_filter.mp h).2
  have cap := Set.ncard_le_ncard sub
  rw [Set.ncard_coe_finset] at cap
  have qty : (T.card:ℤ)≤(p:ℤ) := by exact_mod_cast small
  have fee := mul_le_mul_of_nonneg_right qty (show 0≤(p:ℤ)-1 by omega)
  change (∑x∈T,w x)≤(p:ℤ)*((p:ℤ)-1)+(A.ncard:ℤ)
  omega

#print axioms omit_half_cap_largest
#print axioms omitted_even_weight_bound
end JSP452Audit.StarHost
