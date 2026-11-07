import EveryWinningHeadSurvivesOnTheSameSmallerGapOneSuccessor
namespace JSP452Audit.StarHost

theorem one_gap_three_head_cost (Z N c ρ R b l i L w:ℕ) (G g:ℤ)
    (os:N=2*Z+c) (room:11*c≤2*Z) (root:c+1≤R+ρ) (rp:0<R) (rho:0<ρ) (credit:G≤-3*(ρ:ℤ))
    (allow:l=max (N/5) (R+b)) (cut:i=l-R) (hi:l≤N/3)
    (wide:(Z:ℤ)+b+1≤(L:ℤ)+G) (width:L≤w+N/4+i)
    (cost:g+b+1≤G+2*((N/3-l:ℕ):ℤ)+((N/4-l:ℕ):ℤ)+((N/5-l:ℕ):ℤ)+i) :
    g+22≤11*(w:ℤ) := by
  have cutZ : i+R=l := by omega
  by_cases low:R+b≤N/5
  · rw [max_eq_left low] at allow;omega
  · rw [max_eq_right (by omega : N/5≤R+b)] at allow;omega

theorem one_gap_three_head_selector_false (A p w e:ℕ) (g:ℤ) (big:9≤A) (half:p=(A+1)/2)
    (nonneg:0≤g) (upper:g+22≤11*(w:ℤ)) (three:A*w≤2*e)
    (selector:((A:ℤ)-1)*e≤2*(p:ℤ)*(p+1)+2*g) : False := by
  have wide : 2≤w := by omega
  have floor : 2*(p:ℤ)≤A+1 := by omega
  have prod := mul_le_mul floor (show 2*(p:ℤ)+2≤A+3 by omega) (by positivity) (by positivity)
  have a : (A:ℤ)*w≤2*e := by exact_mod_cast three
  have tax := mul_le_mul_of_nonneg_left a (show (0:ℤ)≤A-1 by omega)
  have base := mul_nonneg (show (0:ℤ)≤(A:ℤ)-9 by omega) (show (0:ℤ)≤(A:ℤ)+3 by positivity)
  have coef : 0≤(A:ℤ)*A-A-44 := by nlinarith only [base,show (9:ℤ)≤A by omega]
  have higher := mul_nonneg coef (show (0:ℤ)≤(w:ℤ)-2 by omega)
  nlinarith only [selector,upper,prod,tax,base,higher]

#print axioms one_gap_three_head_cost
#print axioms one_gap_three_head_selector_false
end JSP452Audit.StarHost