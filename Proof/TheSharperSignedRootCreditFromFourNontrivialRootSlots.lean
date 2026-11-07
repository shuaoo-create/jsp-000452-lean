import ExactlyThreeOriginalHeadGapRegimesRemainForTheOfficialEquation
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem odd_root_fee_with_four_slots {A:Type u} [Finite A] {G:SimpleGraph A} {p q h:ℕ} {K:DegreeRegion G (p+q)}
    {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (low:5≤p) (cap:∀x,Nat.card (G.neighborSet x)≤p+q)
    (bill:(p-1)*P.shortfall+(p+q-1)*h≤q*P.excess) :
    8*P.gamma h+(3*((p:ℤ)+q)+5)*P.excess+((p:ℤ)+q-9)*h+4*P.beta≤0 := by
  have short := Nat.mul_le_mul_right P.shortfall (show 4≤p-1 by omega)
  have blue := Nat.mul_le_mul_right P.excess (show q≤p+q-5 by omega)
  have lim : 4*P.shortfall+(p+q-1)*h≤(p+q-5)*P.excess := by omega
  have cast : (4:ℤ)*P.shortfall+((p+q-1:ℕ):ℤ)*h≤((p+q-5:ℕ):ℤ)*P.excess := by exact_mod_cast lim
  rw [Nat.cast_sub (by omega : 1≤p+q),Nat.cast_sub (by omega : 5≤p+q)] at cast
  push_cast at cast
  have hand := (P.exact_weight_and_root_cost E cap h).2.1
  push_cast at hand;linarith only [hand,cast]

theorem even_root_fee_with_four_slots {A:Type u} [Finite A] {G:SimpleGraph A} {p q h:ℕ} {K:DegreeRegion G (p+q)}
    {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (live:0<k) (low:5≤p) (ord:p≤q)
    (cap:∀x,Nat.card (G.neighborSet x)≤p+q)
    (bill:(p-1)*P.shortfall+(p+q-2)*h≤(q-p)*P.excess+2*(p-1)*(oddRegularComponents G (p+q)).ncard) :
    8*P.gamma h+(3*((p:ℤ)+q)+2)*P.excess+((p:ℤ)+q-10)*h+4*P.beta≤0 := by
  have short := Nat.mul_le_mul_right P.shortfall (show 4≤p-1 by omega)
  have odd := Nat.mul_le_mul_left (2*(p-1)) (P.includes_odd_regular_excess live E)
  have total : (q-p)*P.excess+2*(p-1)*P.excess=(p+q-2)*P.excess := by rw [←Nat.add_mul];congr 1;omega
  have lim : 4*P.shortfall+(p+q-2)*h≤(p+q-2)*P.excess := by omega
  have cast : (4:ℤ)*P.shortfall+((p+q-2:ℕ):ℤ)*h≤((p+q-2:ℕ):ℤ)*P.excess := by exact_mod_cast lim
  rw [Nat.cast_sub (by omega : 2≤p+q)] at cast;push_cast at cast
  have hand := (P.exact_weight_and_root_cost E cap h).2.1
  push_cast at hand;linarith only [hand,cast]

#print axioms odd_root_fee_with_four_slots
#print axioms even_root_fee_with_four_slots
end JSP452Audit.StarHost
