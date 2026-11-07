import EveryLegalWholeCoreDescentMustPassTheExactFullHistoryPrice
namespace JSP452Audit.StarHost

theorem cover_tax_ratio (N r x y a b:ℕ) (px:0<x) (py:0<y)
    (ratio:a*(x+y)≤b*(x*y+x+y)) : a*coveredCoordinateTax N r x y≤b*N := by
  let den := x*y+x+y
  let tax := coveredCoordinateTax N r x y
  have denpos : 0<den := by dsimp [den];omega
  have bound : tax*den≤N*(x+y) := (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  apply Nat.le_of_mul_le_mul_right _ denpos
  · calc
      a*tax*den=a*(tax*den) := by ring
      _ ≤ a*(N*(x+y)) := Nat.mul_le_mul_left a bound
      _ = N*(a*(x+y)) := by ring
      _ ≤ N*(b*den) := Nat.mul_le_mul_left N ratio
      _ = b*N*den := by ring

theorem actual_tax_when_mixed (Z N c r x y:ℕ) (sz:N=2*Z+c) (fit:5*N≤11*Z)
    (px:0<x) (py:0<y) :
    8*actualCoordinateLoss Z N r x y≤8*Z+(if x+y=4 then 4*c else 0) := by
  unfold actualCoordinateLoss
  split_ifs with unit four four
  · omega
  · omega
  all_goals have x2 : 2≤x := by omega
  all_goals have y2 : 2≤y := by omega
  · have ratio : 2*(x+y)≤1*(x*y+x+y) := by
      have xeq : x=2 := by omega
      have yeq : y=2 := by omega
      simp [xeq,yeq]
    have frac := cover_tax_ratio N r x y 2 1 px py ratio
    dsimp only [pointCoordinateTax]
    omega
  · have ratio : 11*(x+y)≤5*(x*y+x+y) := by
      by_cases high:3≤x
      · obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le high
        obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le y2
        nlinarith only [Nat.zero_le u,Nat.zero_le v,Nat.zero_le (u*v)]
      · have highY : 3≤y := by omega
        obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le x2
        obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le highY
        nlinarith only [Nat.zero_le u,Nat.zero_le v,Nat.zero_le (u*v)]
    have frac := cover_tax_ratio N r x y 11 5 px py ratio
    dsimp only [pointCoordinateTax];omega

theorem actual_tax_when_both_large (Z N r x y:ℕ) (fit:16*N≤35*Z) (px:5≤x) (py:5≤y) :
    8*actualCoordinateLoss Z N r x y≤5*Z := by
  have ratio : 7*(x+y)≤2*(x*y+x+y) := by
    obtain ⟨u,rfl⟩ := Nat.exists_eq_add_of_le px
    obtain ⟨v,rfl⟩ := Nat.exists_eq_add_of_le py
    nlinarith only [Nat.zero_le u,Nat.zero_le v,Nat.zero_le (u*v)]
  have frac := cover_tax_ratio N r x y 7 2 (by omega) (by omega) ratio
  have single (a:ℕ) (large:5≤a) : 6*(N/(a+1))≤N := calc
    6*(N/(a+1)) ≤ (a+1)*(N/(a+1)) := Nat.mul_le_mul_right _ (by omega)
    _ ≤ N := Nat.mul_div_le _ _
  have mx := single x px
  have my := single y py
  rw [actualCoordinateLoss,if_neg (by omega)]
  dsimp only [pointCoordinateTax];omega

#print axioms cover_tax_ratio
#print axioms actual_tax_when_mixed
#print axioms actual_tax_when_both_large
end JSP452Audit.StarHost
