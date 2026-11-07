import TheActualLastSurvivingColumnOnTheFixedFourGapSuccessor
namespace JSP452Audit.StarHost

theorem fourth_gap_price_alternatives (D Z c rho h R w:ℕ) (credit gain:ℤ)
    (deg:11≤D) (rp:1≤rho) (hp:1≤h) (start:1≤R) (components:c+1≤R+rho) (fit:11*c≤2*Z)
    (signed:4*credit+((D:ℤ)+2)*rho+((D:ℤ)-6)*h≤0) (baseline:0≤gain) :
    let N := 2*Z+c
    let l := N/6
    let i := l-R
    let M := threeSmallCaps N
    let q := (D:ℤ)-3
    gain+3*Z+3*l+1≤credit+2*M+3*i →
    Z+1≤w+i+N/4 →
    (gain+3*Z+3*l+1+i≤credit+2*M+3*i ∨ 2*(q-2)*w-q*(q+2)≤4*gain) → False := by
  intro N l i M q upper width choice
  have full : 60*M≤47*N := by dsimp only [M,threeSmallCaps];omega
  have lfloor : 6*l≤N ∧ N≤6*l+5 := by dsimp only [l];omega
  have base : credit≤-(rho:ℤ) := by
    have a := mul_nonneg (show (0:ℤ)≤(D:ℤ)-2 by omega) (show (0:ℤ)≤rho by positivity)
    have b := mul_nonneg (show (0:ℤ)≤(D:ℤ)-6 by omega) (show (0:ℤ)≤h by positivity)
    linarith only [signed,a,b]
  have strong : 15*(D:ℤ)-87≤ -30*credit-57*rho := by
    have a := mul_nonneg (show (0:ℤ)≤15*(D:ℤ)-84 by omega) (show (0:ℤ)≤(rho:ℤ)-1 by omega)
    have b := mul_nonneg (show (0:ℤ)≤(D:ℤ)-6 by omega) (show (0:ℤ)≤(h:ℤ)-1 by omega)
    linarith only [signed,a,b]
  have order : N=2*Z+c := rfl
  by_cases idle:i=0
  · omega
  have steps : i+R=l := by dsimp only [i] at idle ⊢;omega
  rcases choice with extra|cold
  · omega
  have plateau : (10:ℤ)*gain+5*D+27≤8*w := by omega
  dsimp only [q] at cold
  have up := mul_le_mul_of_nonneg_left plateau (show (0:ℤ)≤(D:ℤ)-5 by omega)
  have gainCost := mul_nonneg (show (0:ℤ)≤10*((D:ℤ)-5)-16 by omega) baseline
  have pos := mul_nonneg (show (0:ℤ)≤(D:ℤ)-11 by omega) (show (0:ℤ)≤(D:ℤ)+29 by omega)
  linarith only [up,cold,gainCost,pos]

#print axioms fourth_gap_price_alternatives
end JSP452Audit.StarHost
