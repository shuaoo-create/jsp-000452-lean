import RecoverBothActualThirdGapNonpeakWidthsAtTheirWinningHeights
namespace JSP452Audit.StarHost

theorem four_head_root_corrected_point (Z N c rho r x y:ℕ) (size:N=2*Z+c) (volume:11*c≤2*Z) (roots:c≤r+rho)
    (hx:4≤x) (hy:4≤y) (height:11≤x+y) :
    actualCoordinateLoss Z N r x y+N/5≤Z+rho := by
  have basic : 2*(N/5)≤Z := by omega
  have rx : min Z (N/(x+1))≤N/5 := (Nat.min_le_right _ _).trans (Nat.div_le_div_left (by omega) (by decide))
  have ry : min Z (N/(y+1))≤N/5 := (Nat.min_le_right _ _).trans (Nat.div_le_div_left (by omega) (by decide))
  have rate (a b:ℕ) (xlo:a≤x) (ylo:b≤y) (a5:5≤2*a) (b5:5≤2*b) (score:5*(a+b)≤2*(a*b)) :
      5*(x+y)≤2*(x*y) := by
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le xlo
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le ylo
    have xi := Nat.mul_le_mul_right i b5
    have yj := Nat.mul_le_mul_right j a5
    nlinarith only [xi,yj,score,Nat.zero_le (i*j)]
  have good : 5*(x+y)≤2*(x*y) := by
    by_cases a:x=4
    · exact rate 4 7 hx (by omega) (by decide) (by decide) (by decide)
    by_cases b:y=4
    · exact rate 7 4 (by omega) hy (by decide) (by decide) (by decide)
    exact rate 5 5 (by omega) (by omega) (by decide) (by decide) (by decide)
  let den := x*y+x+y
  let J := coveredCoordinateTax N r x y
  have denpos : 0<den := by dsimp [den];omega
  have split : J+N/5≤Z+rho := by
    by_cases live:(r+1)*x*y≤N*(x+y)
    · have cash : J*den+(r+1)*x*y≤N*(x+y) := by
        have h : J*den≤N*(x+y)-(r+1)*x*y := Nat.div_mul_le_self _ _;omega
      have scale : 7*J+5*(r+1)≤2*N := by
        apply Nat.le_of_mul_le_mul_right _ denpos
        calc
          (7*J+5*(r+1))*den=7*(J*den)+(r+1)*(5*den) := by ring
          _ ≤ 7*(J*den)+(r+1)*(7*(x*y)) := Nat.add_le_add_left (Nat.mul_le_mul_left _ (by dsimp [den];omega)) _
          _ = 7*(J*den+(r+1)*x*y) := by ring
          _ ≤ 7*(N*(x+y)) := Nat.mul_le_mul_left _ cash
          _ = N*(7*(x+y)) := by ring
          _ ≤ N*(2*den) := Nat.mul_le_mul_left _ (by dsimp [den];omega)
          _ = 2*N*den := by ring
      omega
    · have zero : J=0 := by dsimp only [J,coveredCoordinateTax];rw [Nat.sub_eq_zero_of_le (by omega),Nat.zero_div]
      omega
  rw [actualCoordinateLoss,if_neg (by omega)]
  change max (max _ _) J+N/5≤Z+rho
  omega

#print axioms four_head_root_corrected_point
end JSP452Audit.StarHost
