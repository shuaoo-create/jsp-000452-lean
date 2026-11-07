import KeepThePositiveWholeCoresAndAllRootChargesOnTheWeightedRegion
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem odd_package_exact_credit {X:Type u} [Finite X] {G:SimpleGraph X} {p q h:ℕ} (K:DegreeRegion G (p+q))
    (P:ScaledPortPlan K q (p-1)) (E:PortGraphLayers P)
    (odd:Odd (p+q)) (a:Odd p) (lower:3≤p) (positive:0<h) (blue:0<q)
    (cap:∀v,Nat.card (G.neighborSet v)≤p+q) (S T:Set X) (apart:Disjoint S T)
    (need:(h:ℤ)≤originalFactorCut G p q S T) :
    (p-1)*P.shortfall+(p+q-1)*h≤q*P.excess ∧ h+1≤P.excess ∧
    4*P.gamma h+((p:ℤ)+q+3)*P.excess+((p:ℤ)+q-5)*h+2*P.beta≤0 := by
  have obstruction := odd_scaled_factor_failure K P E odd a (by omega) cap S T apart need
  have tight := (P.exact_excess E).2
  have bill : (p-1)*P.shortfall+(p+q-1)*h≤q*P.excess := by omega
  have cheap := Nat.mul_le_mul_right P.shortfall (show 2≤p-1 by omega)
  have capQ (x:ℕ) : q*x≤(p+q-3)*x := Nat.mul_le_mul_right x (by omega)
  have gain : h+1≤P.excess := by
    by_contra! few
    have sub := Nat.mul_le_mul_left q (show P.excess≤h by omega)
    have lowerProd := Nat.mul_lt_mul_of_pos_right (show q<p+q-1 by omega) positive
    omega
  have fin : 2*P.shortfall+(p+q-1)*h≤(p+q-3)*P.excess := by have := capQ P.excess;omega
  have zn : ((2:ℤ)*P.shortfall+((p:ℤ)+q-1)*h)≤((p:ℤ)+q-3)*P.excess := by
    have cast : (2:ℤ)*P.shortfall+((p+q-1:ℕ):ℤ)*h≤((p+q-3:ℕ):ℤ)*P.excess := by exact_mod_cast fin
    rw [Nat.cast_sub (by omega : 1≤p+q),Nat.cast_sub (by omega : 3≤p+q)] at cast
    push_cast at cast;exact cast
  have hand := (P.exact_weight_and_root_cost E cap h).2.1
  push_cast at hand
  refine ⟨bill,gain,?_⟩
  linarith only [zn,hand]

#print axioms odd_package_exact_credit
end JSP452Audit.StarHost
