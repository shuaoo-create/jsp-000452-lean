import TheThreeHeadAlternativePaysItsActualTopExposure
namespace JSP452Audit.StarHost

theorem third_gap_price_alternatives (D Z c rho h R w:ℕ) (credit gain:ℤ)
    (deg:11≤D) (rp:1≤rho) (hp:1≤h) (start:1≤R) (components:c+1≤R+rho) (fit:11*c≤2*Z)
    (signed:8*credit+(3*(D:ℤ)+2)*rho+((D:ℤ)-10)*h≤0)
    (eleven:D=11 → 8*credit+(3*(D:ℤ)+5)*rho+((D:ℤ)-9)*h≤0) (base:0≤gain) :
    let N := 2*Z+c
    let l := N/5
    let i := l-R
    let M := N/3+N/4
    let H := (D:ℤ)-3
    gain+2*Z+2*l+1≤credit+2*M+2*i →
    (gain+2*Z+2*l+1+i≤credit+2*M+2*i ∨
      (Z+1≤w+i+N/4 ∧ H*(H-1)*w-(H+1)*(H+3)≤4*gain) ∨
      (Z+1≤w+i+l ∧ 2*(H-1)*w-(H+1)*(H+3)≤4*gain)) → rho=1 := by
  intro N l i M H price alternatives
  have full : 12*M≤7*N := by dsimp only [M];omega
  have floor : 5*l≤N ∧ N≤5*l+4 := by dsimp only [l];omega
  have order : N=2*Z+c := rfl
  have strong : 16*(rho:ℤ)≤ -6*credit := by
    have a := mul_nonneg (show (0:ℤ)≤3*(D:ℤ)-30 by omega) (show (0:ℤ)≤rho by positivity)
    have b := mul_nonneg (show (0:ℤ)≤(D:ℤ)-10 by omega) (show (0:ℤ)≤h by positivity)
    linarith only [signed,a,b,show (0:ℤ)≤rho by positivity]
  by_cases idle:i=0
  · omega
  have steps : i+R=l := by dsimp only [i] at idle ⊢;omega
  rcases alternatives with warm|⟨low,three⟩|⟨low,large⟩
  · omega
  · have live : 6*gain+58≤20*(w:ℤ) := by omega
    have hw : 2≤w := by omega
    have slim : 4*gain<14*((w:ℤ)-2) := by omega
    have head : 8≤H := by dsimp only [H];omega
    have monot : 14≤H*(H-1) := by nlinarith only [mul_nonneg (show 0≤H-8 by omega) (show 0≤H-1 by omega),head]
    have supply := mul_le_mul_of_nonneg_right monot (show (0:ℤ)≤(w:ℤ)-2 by omega)
    have poly := mul_nonneg (show 0≤H-8 by omega) (show 0≤H+2 by omega)
    exfalso;linarith only [poly,supply,three,slim]
  · by_contra! bad
    have two : 2≤rho := by omega
    have bound : 21*(D:ℤ)-106≤ -24*credit-44*rho := by
      have a := mul_nonneg (show (0:ℤ)≤9*(D:ℤ)-38 by omega) (show (0:ℤ)≤(rho:ℤ)-2 by omega)
      have b := mul_nonneg (show (0:ℤ)≤(D:ℤ)-10 by omega) (show (0:ℤ)≤(h:ℤ)-1 by omega)
      linarith only [signed,a,b]
    have height : 24*gain+21*D+46≤40*(w:ℤ) := by omega
    by_cases lower:D≤12
    · rcases (show D=11 ∨ D=12 by omega) with a|a
      · have extra := eleven a
        dsimp only [H] at large;rw [a] at extra large
        norm_num at extra large
        omega
      · dsimp only [H] at large;rw [a] at large height
        norm_num at large height;omega
    · have big : 13≤D := by omega
      have up := mul_le_mul_of_nonneg_left height (show (0:ℤ)≤(D:ℤ)-4 by omega)
      have income := mul_nonneg (show (0:ℤ)≤24*((D:ℤ)-4)-80 by omega) base
      have pos := mul_nonneg (show (0:ℤ)≤(D:ℤ)-13 by omega) (show (0:ℤ)≤(D:ℤ)+15 by omega)
      dsimp only [H] at large
      linarith only [large,up,income,pos]

#print axioms third_gap_price_alternatives
end JSP452Audit.StarHost
