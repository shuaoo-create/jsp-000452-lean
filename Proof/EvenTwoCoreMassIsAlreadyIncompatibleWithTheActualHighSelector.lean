import TheOddDegreeDeficiencyUsesStrictlyMorePositiveComponents
namespace JSP452Audit.StarHost

theorem gap_two_even_two_core_price_false (p Z R b l i L w e:ℕ) (G g:ℤ) (deg:5≤p) (rp:0<R)
    (mass:6*p+9≤Z) (credit:2*G+3*p+2≤0) (allow:l=max ((2*Z+2)/5) (R+b)) (cut:i=l-R)
    (high:Z<L) (width:L≤w+i+l) (nonneg:0≤g) (actual:w≤e)
    (cost:g+Z+2*l+R+b+1≤G+2*(((2*Z+2)/3:ℕ):ℤ)+2*(((2*Z+2)/4:ℕ):ℤ))
    (sel:(2*(p:ℤ)-1)*e≤2*(p:ℤ)*(p+1)+2*g) : False := by
  let N := 2*Z+2
  have a : 3*((N/3:ℕ):ℤ)≤N := by omega
  have t : 4*((N/4:ℕ):ℤ)≤N := by omega
  have sz : (N:ℤ)=2*Z+2 := by dsimp only [N];push_cast;rfl
  have step : (i:ℤ)+R=l := by omega
  have value : (Z:ℤ)+1≤(w:ℤ)+i+l := by omega
  have rpos : (1:ℤ)≤R := by omega
  have bpos : (0:ℤ)≤b := by positivity
  have big : 6*(p:ℤ)+9≤Z := by exact_mod_cast mass
  have pe : (5:ℤ)≤p := by exact_mod_cast deg
  have EW := mul_le_mul_of_nonneg_left (show (w:ℤ)≤e by exact_mod_cast actual) (show (0:ℤ)≤2*(p:ℤ)-1 by omega)
  have S : (2*(p:ℤ)-1)*w≤2*(p:ℤ)*(p+1)+2*g := EW.trans sel
  change g+Z+2*l+R+b+1≤G+2*((N/3:ℕ):ℤ)+2*((N/4:ℕ):ℤ) at cost
  by_cases low:R+b≤N/5
  · change l=max (N/5) (R+b) at allow
    rw [max_eq_left low] at allow
    have la : 5*(l:ℤ)≤N := by omega
    have lb : (N:ℤ)≤5*(l:ℤ)+4 := by omega
    have fundamental : (Z:ℤ)+5*R+1≤5*(w:ℤ) := by linarith only [step,value,la,sz]
    have gain : 15*g≤15*G+40*w-31 := by linarith only [cost,sz,a,t,lb,fundamental,rpos,bpos]
    have ceil : (30*(p:ℤ)-95)*w≤30*(p:ℤ)*p-15*p-92 := by linarith only [gain,S,credit]
    have wide : 6*(p:ℤ)+15≤5*(w:ℤ) := by linarith only [fundamental,big,rpos]
    have scale := mul_le_mul_of_nonneg_left wide (show (0:ℤ)≤30*(p:ℤ)-95 by omega)
    have tiny : p≤6 := by
      by_contra! no
      have delta := mul_nonneg (show (0:ℤ)≤(p:ℤ)-7 by omega) (show (0:ℤ)≤30*(p:ℤ)+165 by positivity)
      nlinarith only [scale,ceil,delta]
    have finish (fixed:p=5 ∨ p=6) : False := by
      rcases fixed with eq|eq <;> subst p <;> norm_num at ceil S credit mass
      all_goals have lim : Z≤44 := by omega
      all_goals clear scale
      all_goals dsimp only [N] at allow cost
      all_goals interval_cases Z <;> norm_num at * <;> omega
    exact finish (by omega)
  · change l=max (N/5) (R+b) at allow
    rw [max_eq_right (by omega : N/5≤R+b)] at allow
    have eq : (l:ℤ)=R+b := by exact_mod_cast allow
    have up : 2*g≤3*((w:ℤ)-p-3) := by linarith only [value,step,cost,eq,a,t,sz,rpos,credit,big,pe]
    have wide : 0≤(w:ℤ)-p-3 := by omega
    have excess := mul_nonneg (show (0:ℤ)≤2*(p:ℤ)-4 by omega) wide
    nlinarith only [S,up,excess,pe]

#print axioms gap_two_even_two_core_price_false
end JSP452Audit.StarHost