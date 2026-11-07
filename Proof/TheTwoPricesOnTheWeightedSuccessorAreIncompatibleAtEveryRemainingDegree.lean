import RealizeTheJointWeightedDeletionAndLowerTheActualCoreDegree
namespace JSP452Audit.StarHost

theorem gap_one_weighted_price_contradiction (D H h ρ Z k b L e t p:ℕ) (G g:ℤ)
    (degree:11≤D) (gap:D=H+1) (half:p=H/2) (size:0<h) (supply:h≤ρ)
    (odd:D%2=1 → h+1≤ρ)
    (credit:4*G+((D:ℤ)+2)*ρ+((D:ℤ)-6)*h≤0)
    (width:(Z:ℤ)+b+1≤(L:ℤ)+G) (seen:L≤k+b+e)
    (weighted:3*(D-1)*k+2*t≤3*(D-1)*Z)
    (bill:g+(D:ℤ)*Z+1≤G+(D:ℤ)*k+t)
    (sel:((H:ℤ)-2)*e≤2*(p:ℤ)*(p+1)+2*g) : False := by
  have root := gap_two_linear_degree_credit D h ρ G degree size supply credit
  have high : (Z:ℤ)-k+1-G≤e := by omega
  have fee : 3*((D:ℤ)-1)*k+2*t≤3*((D:ℤ)-1)*Z := by
    rw [←show ((D-1:ℕ):ℤ)=(D:ℤ)-1 by omega];exact_mod_cast weighted
  have product := mul_le_mul_of_nonneg_left high (show (0:ℤ)≤(H:ℤ)-2 by omega)
  have eq : (D:ℤ)=H+1 := by exact_mod_cast gap
  rw [eq] at fee bill
  have necessary : (H:ℤ)*(1-G)≤2*(p:ℤ)*(p+1) := by linarith only [fee,bill,sel,product]
  by_cases even:H=2*p
  · have oddD : D%2=1 := by omega
    have double := odd oddD
    have strong : (p:ℤ)+2≤1-G := by omega
    have scale := mul_le_mul_of_nonneg_left strong (show (0:ℤ)≤H by positivity)
    rw [show (H:ℤ)=2*p by exact_mod_cast even] at necessary scale
    nlinarith only [necessary,scale,show (0:ℤ)<p by omega]
  · have alt : H=2*p+1 := by omega
    have strong : (p:ℤ)+1≤1-G := by omega
    have scale := mul_le_mul_of_nonneg_left strong (show (0:ℤ)≤H by positivity)
    rw [show (H:ℤ)=2*p+1 by exact_mod_cast alt] at necessary scale
    nlinarith only [necessary,scale,show (0:ℤ)≤p by positivity]

#print axioms gap_one_weighted_price_contradiction
end JSP452Audit.StarHost