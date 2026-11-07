import RecoverBothActualWinningHeadTypesOnTheCommonHighSuccessor
namespace JSP452Audit.StarHost

theorem gap_two_three_head_cost_ceiling (Z N c ρ R b l i L w:ℕ) (G g:ℤ)
    (size:N=2*Z+c) (room:11*c≤2*Z) (roots:c+1≤R+ρ) (rp:0<R)
    (credit:4*G+13*ρ≤0) (allow:l=max (N/5) (R+b)) (cut:i=l-R)
    (high:Z<L) (width:L≤w+i+N/4)
    (cost:g+Z+2*l+R+b+1≤G+2*((N/3:ℕ):ℤ)+2*((N/4:ℕ):ℤ)) :
    g+7≤6*(w:ℤ) := by
  have available : R≤l := by omega
  have exactCut : i+R=l := by omega
  by_cases low:R+b≤N/5
  · rw [max_eq_left low] at allow
    omega
  · rw [max_eq_right (by omega : N/5≤R+b)] at allow
    omega

theorem gap_two_three_head_selector_false (H p w e:ℕ) (g:ℤ) (head:9≤H) (half:p=(H+1)/2)
    (nonneg:0≤g) (upper:g+7≤6*(w:ℤ)) (three:H*w≤2*e)
    (selector:((H:ℤ)-1)*e≤2*(p:ℤ)*(p+1)+2*g) : False := by
  have wide : 2≤w := by omega
  have floor : 2*(p:ℤ)≤H+1 := by omega
  have prod := mul_le_mul floor (show 2*(p:ℤ)+2≤H+3 by omega) (by positivity) (by positivity)
  have a : (H:ℤ)*w≤2*e := by exact_mod_cast three
  have tax := mul_le_mul_of_nonneg_left a (show (0:ℤ)≤H-1 by omega)
  have base := mul_nonneg (show (0:ℤ)≤(H:ℤ)-9 by omega) (show (0:ℤ)≤(H:ℤ)+3 by positivity)
  have coef : 0≤(H:ℤ)*H-H-24 := by nlinarith only [base,show (9:ℤ)≤H by omega]
  have higher := mul_nonneg coef (show (0:ℤ)≤(w:ℤ)-2 by omega)
  nlinarith only [selector,upper,prod,tax,base,higher]

theorem gap_two_four_head_cost_ceiling (Z N c ρ R b l i L w:ℕ) (G g:ℤ)
    (size:N=2*Z+c) (room:11*c≤2*Z) (roots:c+1≤R+ρ) (rp:0<R) (zpos:2≤Z) (posρ:0<ρ)
    (allow:l=max (N/5) (R+b)) (cut:i=l-R)
    (extra:(Z:ℤ)+b+1≤(L:ℤ)+G) (width:L≤w+i+l)
    (cost:g+Z+2*l+R+b+1≤G+2*((N/3:ℕ):ℤ)+2*((N/4:ℕ):ℤ)) :
    g≤3*(w:ℤ)+4*G+2*ρ-8 := by
  have exactCut : i+R=l := by omega
  by_cases low:R+b≤N/5
  · rw [max_eq_left low] at allow
    omega
  · rw [max_eq_right (by omega : N/5≤R+b)] at allow
    omega

theorem gap_two_four_head_selector_false (H p w e h ρ:ℕ) (G g:ℤ) (head:9≤H) (half:p=(H+1)/2)
    (pos:0<h) (hp:h≤ρ) (credit:4*G+((H:ℤ)+4)*ρ+((H:ℤ)-4)*h≤0)
    (nonneg:0≤g) (upper:g≤3*(w:ℤ)+4*G+2*ρ-8) (actual:w≤e)
    (selector:((H:ℤ)-1)*e≤2*(p:ℤ)*(p+1)+2*g) : False := by
  have a := mul_nonneg (show (0:ℤ)≤(H:ℤ)+2 by positivity) (show (0:ℤ)≤(ρ:ℤ)-1 by omega)
  have b := mul_nonneg (show (0:ℤ)≤(H:ℤ)-4 by omega) (show (0:ℤ)≤(h:ℤ)-1 by omega)
  have ceiling : g≤3*((w:ℤ)-p-3) := by linarith only [a,b,upper,credit,show (3:ℤ)*p+3≤2*H by omega]
  have aw := mul_le_mul_of_nonneg_left (show (w:ℤ)≤e by exact_mod_cast actual) (show (0:ℤ)≤(H:ℤ)-1 by omega)
  have trim := mul_nonneg (show (0:ℤ)≤(H:ℤ)-7 by omega) (show (0:ℤ)≤(w:ℤ)-p-3 by omega)
  have base := mul_le_mul_of_nonneg_right (show 2*(p:ℤ)-2≤(H:ℤ)-1 by omega) (show (0:ℤ)≤(p:ℤ)+3 by positivity)
  nlinarith only [selector,aw,trim,base,ceiling,show (5:ℤ)≤p by omega]

#print axioms gap_two_three_head_cost_ceiling
#print axioms gap_two_three_head_selector_false
#print axioms gap_two_four_head_cost_ceiling
#print axioms gap_two_four_head_selector_false
end JSP452Audit.StarHost