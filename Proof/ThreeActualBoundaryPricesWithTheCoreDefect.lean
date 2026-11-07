import ActualBlueClassAndUnitCostsAtTheTwoNineBoundary
namespace JSP452Audit.StarHost
open SimpleGraph
theorem last_boundary_with_core_defect (t r a μ V v u δ d ρ h β g₂ g₃ gb w₂ w₃ wD c₂ c₃ cD : ℕ)
    (width : h≤ρ) (deficit : ρ≤d+1) (head : gb≤r+ρ) (order : gb≤g₃ ∧ g₃≤g₂ ∧ g₂≤t)
    (inner : t≤μ) (buffer : 6*ρ+6≤β)
    (origVolume : μ≤u+a+ρ+3*δ) (tail : V+a+r+2*d+δ≤u) (allUnits : v=0 → μ≤3*V+a+ρ)
    (top : 2*wD+a+2*V+2*r+2≤cD+2*gb)
    (two : c₂<2*w₂ → 2*w₂+2*(u+δ+g₂)≤c₂+2*t ∧
      (0<v → 2*w₂+V+v+u+δ+g₂≤c₂+t))
    (three : c₃<2*w₃ → 2*w₃+2*(u+δ+g₃)≤c₃+2*g₂ ∧
      (0<v → 2*w₃+V+v+u+δ+g₃≤c₃+g₂)) :
    2*w₂+2*w₃+2*wD+2*h≤c₂+c₃+cD+β+2*δ := by
  rcases order with ⟨ord₁,ord₂,ord₃⟩
  by_cases empty : v=0
  · have volume := allUnits empty
    by_cases e₂ : c₂<2*w₂ <;> by_cases e₃ : c₃<2*w₃
    · have b := (two e₂).1;have c := (three e₃).1;omega
    · have b := (two e₂).1;omega
    · have c := (three e₃).1;omega
    · omega
  · have pos : 0<v := by omega
    by_cases e₂ : c₂<2*w₂ <;> by_cases e₃ : c₃<2*w₃
    · have b := (two e₂).2 pos;have c := (three e₃).2 pos;omega
    · have b := (two e₂).2 pos;omega
    · have c := (three e₃).2 pos;omega
    · omega

theorem fold_last_three_with_fee (D h fee δ : ℕ) (L C : ℕ→ℕ) (deg : 6≤D)
    (three : 2*L 2+2*L 3+2*L D+2*h≤C 2+C 3+C D+fee+2*δ)
    (other : ∀j,4≤j → j<D → 2*L j≤C j) :
    2*(∑z∈Finset.range (D-1),L (z+2))+2*h≤(∑z∈Finset.range (D-1),C (z+2))+fee+2*δ := by
  have price := Finset.sum_le_sum (s:=Finset.range (D-4)) (fun z mem =>
    other (z+4) (by omega) (by have := Finset.mem_range.mp mem;omega))
  rw [←Finset.mul_sum] at price
  rw [split_three_interior_layers D deg L,split_three_interior_layers D deg C]
  omega

#print axioms last_boundary_with_core_defect
#print axioms fold_last_three_with_fee
end JSP452Audit.StarHost
