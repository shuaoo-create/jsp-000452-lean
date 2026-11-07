import TheLastRegularExteriorCapControlsItsRemainingWinningColumn
namespace JSP452Audit.StarHost

theorem regular_third_price_false (P p N i b c f g w₀ w₁ w₂:ℕ)
    (ord:N=2*P+1) (big:6≤p) (room:p≤P) (steps:i<P) (hist:b≤c ∧ c≤f)
    (fee:g+3*P+p+min i f+min i c+min i b≤min (i+P) w₀+min (i+P) w₁+min (i+P) w₂)
    (top:w₂≤b+P+p-3 ∧ w₂≤b+N/5+p-2 ∧ w₂≤c+N/5)
    (middle:(w₁≤c+N/4+p+2 ∧ w₁≤f+N/4) ∨ w₁≤N/4+N/7)
    (last:f ≤ i → w₀≤P ∨ w₀≤g+(p-1)+N/3+i) : False := by
  by_cases all:i≤b
  · omega
  by_cases high:i≤c
  · omega
  by_cases mid:i≤f
  · rcases middle with ⟨a,_⟩|a <;> omega
  rcases last (Nat.le_of_not_ge mid) with zero|small <;> rcases middle with ⟨_,a⟩|a <;> omega

#print axioms regular_third_price_false
end JSP452Audit.StarHost
