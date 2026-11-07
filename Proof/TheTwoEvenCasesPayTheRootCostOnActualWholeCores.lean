import ExactCreditAndStrictlyMoreCoresThanWidthAtEveryOddCap
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem unequal_even_package_exact_credit {X:Type u} [Finite X] {G:SimpleGraph X} {p q h:ℕ} (K:DegreeRegion G (p+q))
    (P:ScaledPortPlan K (q-p) (p-1)) (E:PortGraphLayers P)
    (even:Even (p+q)) (a:Odd p) (low:3≤p) (lt:p<q)
    (cap:∀v,Nat.card (G.neighborSet v)≤p+q) (S T:Set X) (apart:Disjoint S T)
    (need:(h:ℤ)≤originalFactorCut G p q S T) :
    (p-1)*P.shortfall+(p+q-2)*h≤(q-p)*P.excess+2*(p-1)*(oddRegularComponents G (p+q)).ncard ∧
    h≤P.excess ∧ 4*P.gamma h+((p:ℤ)+q+2)*P.excess+((p:ℤ)+q-6)*h+2*P.beta≤0 := by
  have obstruction := even_scaled_factor_failure K P E even a (by omega) lt.le cap S T apart need
  have tight := (P.exact_excess E).2
  have oddCount := P.includes_odd_regular_excess (by omega) E
  have bill : (p-1)*P.shortfall+(p+q-2)*h≤(q-p)*P.excess+2*(p-1)*(oddRegularComponents G (p+q)).ncard := by omega
  have mul := Nat.mul_le_mul_left (2*(p-1)) oddCount
  have total : (q-p)*P.excess+2*(p-1)*P.excess=(p+q-2)*P.excess := by rw [←Nat.add_mul];congr 1;omega
  have cheap := Nat.mul_le_mul_right P.shortfall (show 2≤p-1 by omega)
  have fin : 2*P.shortfall+(p+q-2)*h≤(p+q-2)*P.excess := by omega
  have size : h≤P.excess := Nat.le_of_mul_le_mul_left (by omega : (p+q-2)*h≤(p+q-2)*P.excess) (by omega)
  have zn : (2:ℤ)*P.shortfall+((p:ℤ)+q-2)*h≤((p:ℤ)+q-2)*P.excess := by
    have cast : (2:ℤ)*P.shortfall+((p+q-2:ℕ):ℤ)*h≤((p+q-2:ℕ):ℤ)*P.excess := by exact_mod_cast fin
    rw [Nat.cast_sub (by omega : 2≤p+q)] at cast;push_cast at cast;exact cast
  have hand := (P.exact_weight_and_root_cost E cap h).2.1
  push_cast at hand
  exact ⟨bill,size,by linarith only [zn,hand]⟩

theorem central_even_package_exact_credit {X:Type u} [Finite X] {G:SimpleGraph X} {p h:ℕ} (K:DegreeRegion G (p+p))
    (P:ScaledPortPlan K 1 (K.pieces.ncard+1)) (E:PortGraphLayers P) (pos:3≤p)
    (cap:∀v,Nat.card (G.neighborSet v)≤p+p) (S T:Set X) (apart:Disjoint S T)
    (need:(h:ℤ)≤originalFactorCut G p p S T) :
    P.shortfall=0 ∧ h≤P.excess ∧
      4*P.gamma h+((p:ℤ)+p+1)*P.excess+2*P.beta≤0 := by
  have count := balanced_cut_le_original_odd_regular G p (fun v => (cap v).trans_eq (by omega)) S T apart
  have reg := P.includes_odd_regular_excess (by decide) E
  have same : 2*p=p+p := by omega
  rw [same] at count
  have hbound : h≤P.excess := by omega
  have tight := (P.exact_excess E).2
  have order : P.family.ncard≤K.pieces.ncard := Set.ncard_le_card P.family
  have actual := (P.exact_excess E).1
  have zero : P.shortfall=0 := by
    by_contra! positive
    have lower := Nat.mul_le_mul_left (K.pieces.ncard+1) (show 1≤P.shortfall by omega)
    rw [Nat.mul_one] at lower;omega
  have hand := (P.exact_weight_and_root_cost E cap h).2.1
  rw [zero] at hand
  push_cast at hand
  have gain : ((p:ℤ)+p-5)*P.excess≥0 := mul_nonneg (by omega) (by positivity)
  exact ⟨zero,hbound,by push_cast;linarith only [hand,gain,show (h:ℤ)≤P.excess by exact_mod_cast hbound]⟩

#print axioms unequal_even_package_exact_credit
#print axioms central_even_package_exact_credit
end JSP452Audit.StarHost
