import CountTheOtherActualComponentsBelowTheSingleDominantCore
namespace JSP452Audit.StarHost

theorem gap_two_linear_degree_credit (D h ρ:ℕ) (G:ℤ) (degree:11≤D) (head:0<h) (supply:h≤ρ)
    (sharp:4*G+((D:ℤ)+2)*ρ+((D:ℤ)-6)*h≤0) :
    4*G+2*(D:ℤ)-4+13*((ρ:ℤ)-1)≤0 := by
  have a := mul_nonneg (show (0:ℤ)≤(D:ℤ)-11 by omega) (show (0:ℤ)≤(ρ:ℤ)-1 by omega)
  have b := mul_nonneg (show (0:ℤ)≤(D:ℤ)-6 by omega) (show (0:ℤ)≤(h:ℤ)-1 by omega)
  linarith only [a,b,sharp]

theorem gap_two_selector_separation (q p w e:ℕ) (g:ℤ) (deg:9≤q) (half:p=q/2)
    (nonneg:0≤g) (upper:2*g≤((q:ℤ)-2)*((w:ℤ)-p-3)) (wide:p+3≤w) (actual:w≤e)
    (sel:((q:ℤ)-2)*e≤2*(p:ℤ)*(p+1)+2*g) : False := by
  have mul := mul_le_mul_of_nonneg_left (show (w:ℤ)≤e by exact_mod_cast actual) (show (0:ℤ)≤(q:ℤ)-2 by omega)
  have base := mul_le_mul_of_nonneg_right (show 2*(p:ℤ)-2≤(q:ℤ)-2 by omega) (show (0:ℤ)≤(p:ℤ)+3 by positivity)
  nlinarith only [mul,base,upper,sel,show (4:ℤ)≤p by omega]

#print axioms gap_two_linear_degree_credit
#print axioms gap_two_selector_separation
end JSP452Audit.StarHost