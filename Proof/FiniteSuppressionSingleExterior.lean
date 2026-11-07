import ActualSuppressionBothSuccessors
namespace JSP452Audit.StarHost
open SimpleGraph

theorem finite_core_suppression_choice {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) :
    ∃T:Set X,(∀v,Nat.card (G.neighborSet v)=D → v∈T ∨ ∃w∈T,G.Adj v w) ∧
      (D=7 → 25*T.ncard≤9*Nat.card X) ∧ (D=8 → 3*T.ncard≤Nat.card X) ∧
      (9≤D → 13*T.ncard≤4*Nat.card X) := by
  obtain ⟨T,cover,fee⟩ := quarter_full_core_set G D
  refine ⟨T,cover,?_,?_,?_⟩
  · rintro rfl
    norm_num at fee
    exact_mod_cast (show (25:ℚ)*T.ncard≤9*Nat.card X by linarith only [fee,Nat.cast_nonneg (Nat.card X) (α:=ℚ)])
  · rintro rfl
    norm_num at fee
    exact_mod_cast (show (3:ℚ)*T.ncard≤Nat.card X by linarith only [fee,Nat.cast_nonneg (Nat.card X) (α:=ℚ)])
  · intro big
    have power := pow_le_pow_of_le_one (show 0≤(3/4:ℚ) by norm_num) (show (3/4:ℚ)≤1 by norm_num) (by omega : 10≤D+1)
    have coeff : 1/4+(3/4:ℚ)^(D+1)≤4/13 := by norm_num at power ⊢;linarith
    have mul := mul_le_mul_of_nonneg_right coeff (show (0:ℚ)≤Nat.card X by positivity)
    exact_mod_cast (show (13:ℚ)*T.ncard≤4*Nat.card X by linarith only [fee,mul])

theorem single_exact_suppression_floor {s t r D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (hn : Antitone n) (hm : Antitone m)
    (pm : ∀j,1≤m j) (deg : 0<D) (cap : ∀x,Nat.card (G.neighborSet x)≤D) (head : n ⟨0,hs⟩=D)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    let H := G.induce K.core
    let size := 2*matchingEdges H+K.roots.ncard+minimumExposure G D
    ∃T:Set K.core,(D=7 → 25*T.ncard≤9*size) ∧ (D=8 → 3*T.ncard≤size) ∧
      (9≤D → 13*T.ncard≤4*size) ∧
      ∀j,0<j → j≤D → t-(r+K.roots.ncard+T.ncard)≤uniformEnvelope (G.induce K.rest) j := by
  intro H size
  obtain ⟨T,covers,p7,p8,p9⟩ := finite_core_suppression_choice H D
  have inside (x:K.core) : Nat.card (H.neighborSet x)≤D := (induced_neighbor_count_le G K.core x).trans (cap _)
  obtain ⟨R,sub,small,light⟩ := dominated_full_red_split H D deg inside T covers
  have order : Nat.card ↥K.core=size := (Nat.card_coe_set_eq _).trans K.core_order
  rw [order] at p7 p8 p9
  exact ⟨T,p7,p8,p9,suppressed_core_exterior_floor G K R sub small T.ncard light n m hs hn hm pm head deg row⟩

theorem single_suppression_axis (a μ t r η f w u q : ℕ) (before : r<t) (rank : q+t=μ+1) (axis : w≤f+t-1-r)
    (floor : t-(r+a+η)≤u) : w+max (a+q+r) (μ+1-η)≤a+μ+u+f := by
  rcases le_total (a+q+r) (μ+1-η) with le|le
  · rw [max_eq_right le];omega
  · rw [max_eq_left le];omega

#print axioms finite_core_suppression_choice
#print axioms single_exact_suppression_floor
#print axioms single_suppression_axis
end JSP452Audit.StarHost