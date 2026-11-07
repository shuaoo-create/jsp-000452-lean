import PhysicalEnvelopeHostCopy
namespace JSP452Audit.StarHost
open SimpleGraph

theorem quarter_full_core_set {X : Type*} [Finite X] (H : SimpleGraph X) (D : ℕ) :
    ∃T:Set X,(∀v,Nat.card (H.neighborSet v)=D → v∈T ∨ ∃w∈T,H.Adj v w) ∧
      (T.ncard:ℚ)≤(1/4+(3/4:ℚ)^(D+1))*(Nat.card X:ℚ) := by
  classical
  let _ := Fintype.ofFinite X
  let F := {v:X | Nat.card (H.neighborSet v)=D}
  let N (z:↥F) := insert z.val (H.neighborSet z.val)
  have size (z:↥F) : (N z).ncard=D+1 := by
    have cap : Nat.card (H.neighborSet z.val)=D := z.property
    rw [Nat.card_coe_set_eq] at cap
    exact (Set.ncard_insert_of_notMem (show z.val∉H.neighborSet z.val from H.irrefl)).trans (congrArg (fun x:ℕ => x+1) cap)
  have one (z:↥F) : (N z).Nonempty := ⟨z.val,Set.mem_insert _ _⟩
  obtain ⟨T,hit,fee⟩ := quarter_sample_transversal N one
  have room : (Nat.card ↥F:ℚ)≤Nat.card X := by exact_mod_cast Nat.card_le_card_of_injective (Subtype.val : ↥F→X) Subtype.val_injective
  have scale := mul_le_mul_of_nonneg_right room (show 0≤(3/4:ℚ)^(D+1) by positivity)
  simp_rw [size] at fee
  simp only [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul] at fee
  refine ⟨T,?_,by linarith only [fee,scale]⟩
  intro v full
  obtain ⟨x,mem,close⟩ := hit ⟨v,full⟩
  rcases close with eq|adj
  · left;change x=v at eq;rw [←eq];exact mem
  · exact Or.inr ⟨x,mem,adj⟩

theorem quarter_core_integer_price {X : Type*} [Finite X] (H : SimpleGraph X) (D : ℕ) (deg : 9≤D) :
    ∃T:Set X,(∀v,Nat.card (H.neighborSet v)=D → v∈T ∨ ∃w∈T,H.Adj v w) ∧ 13*T.ncard≤4*Nat.card X := by
  obtain ⟨T,cover,fee⟩ := quarter_full_core_set H D
  have power := pow_le_pow_of_le_one (show 0≤(3/4:ℚ) by norm_num) (show (3/4:ℚ)≤1 by norm_num) (by omega : 10≤D+1)
  have coeff : 1/4+(3/4:ℚ)^(D+1)≤4/13 := by norm_num at power ⊢;linarith
  have mul := mul_le_mul_of_nonneg_right coeff (show (0:ℚ)≤Nat.card X by positivity)
  refine ⟨T,cover,?_⟩
  exact_mod_cast (show (13:ℚ)*T.ncard≤4*Nat.card X by linarith only [fee,mul])

#print axioms quarter_full_core_set
#print axioms quarter_core_integer_price
end JSP452Audit.StarHost