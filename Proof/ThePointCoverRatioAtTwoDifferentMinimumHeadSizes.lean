import OnlySevenOriginalHeadGapsRemainAtEveryPossibleCounterexample
namespace JSP452Audit.StarHost

theorem bounded_point_tax_ratio (Z N r x y a b:ℕ) (ax:2≤a) (byh:2≤b) (left:a≤x) (right:b≤y) :
    (a*b+a+b)*actualCoordinateLoss Z N r x y≤(a+b)*N := by
  have px : 0<x := by omega
  have py : 0<y := by omega
  let den := a*b+a+b
  let num := a+b
  have rate : den*(x+y)≤num*(x*y+x+y) := by
    have one := Nat.mul_le_mul_left (a*x) right
    have two := Nat.mul_le_mul_left (b*y) left
    dsimp only [den,num];nlinarith only [one,two]
  have frac := cover_tax_ratio N r x y den num px py rate
  have red : den≤num*(x+1) := by
    have one := Nat.mul_le_mul_left b left
    dsimp only [den,num];nlinarith only [one,Nat.zero_le (a*x)]
  have blue : den≤num*(y+1) := by
    have one := Nat.mul_le_mul_left a right
    dsimp only [den,num];nlinarith only [one,Nat.zero_le (b*y)]
  have bound (v:ℕ) (fit:den≤num*(v+1)) : den*(min Z (N/(v+1)))≤num*N := calc
    _ ≤ den*(N/(v+1)) := Nat.mul_le_mul_left _ (Nat.min_le_right _ _)
    _ ≤ num*(v+1)*(N/(v+1)) := Nat.mul_le_mul_right _ fit
    _ = num*((v+1)*(N/(v+1))) := by ring
    _ ≤ num*N := Nat.mul_le_mul_left _ (Nat.mul_div_le _ _)
  rw [actualCoordinateLoss,if_neg (by omega)]
  change den*(max (max (min Z (N/(x+1))) (min Z (N/(y+1)))) (coveredCoordinateTax N r x y))≤num*N
  have X := bound x red
  have Y := bound y blue
  simp only [max_def];split_ifs <;> assumption

theorem five_column_tax_ratios (Z N r x y:ℕ) (fit:7*N≤15*Z) (a:4≤x) (b:4≤y) (total:12≤x+y) :
    let J := actualCoordinateLoss Z N r x y
    17*J≤5*N ∧ 24*J≤16*Z ∧ (5≤x → 5≤y → 24*J≤15*Z) ∧ (6≤x → 6≤y → 24*J≤13*Z) := by
  intro J
  have rate : 17*J≤5*N := by
    rcases (show 6≤x ∨ 6≤y by omega) with hi|hi
    · have bound := bounded_point_tax_ratio Z N r x y 6 4 (by decide) (by decide) hi b
      change 34*J≤10*N at bound;omega
    · have bound := bounded_point_tax_ratio Z N r x y 4 6 (by decide) (by decide) a hi
      change 34*J≤10*N at bound;omega
  refine ⟨rate,by omega,?_,?_⟩
  · intro hx hy
    have bound := bounded_point_tax_ratio Z N r x y 5 5 (by decide) (by decide) hx hy
    change 35*J≤10*N at bound;omega
  · intro hx hy
    have bound := bounded_point_tax_ratio Z N r x y 6 6 (by decide) (by decide) hx hy
    change 48*J≤12*N at bound;omega

#print axioms bounded_point_tax_ratio
#print axioms five_column_tax_ratios
end JSP452Audit.StarHost
