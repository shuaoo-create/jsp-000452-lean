import PenultimateActualEightPrice
namespace JSP452Audit.StarHost

theorem eight_penultimate_prices_incompatible (P j h L7 L8 b c M2 M3 M4 rho6:ℕ)
    (types:EightSelectionSize j h) (ord:4*j≤P)
    (slots2:3*M2≤2*P+j) (slots3:2*M3≤P) (slots4:5*M4≤2*P+j)
    (price:2*P+4*j+1+b+c≤L7+L8+h)
    (stage:L8-b≤min (P-j) (2*P-7*j)+(22+2*h)/5-2)
    (second:L7≤P ∨ L7-c≤M2+rho6)
    (rho:rho6≤max 3 ((h-1+((22+2*h)/5-2)+9)/2))
    (single:j=1 → L8-b≤max M3 (M4+2))
    (multiple:2≤j → L8-b≤M3+4) : False := by
  unfold EightSelectionSize at types
  rcases types with ⟨rfl,rfl⟩|⟨rfl,small⟩|⟨rfl,rfl⟩
  · have cap := single rfl
    omega
  · have cap := multiple (by decide)
    omega
  · have cap := multiple (by decide)
    omega

#print axioms eight_penultimate_prices_incompatible
end JSP452Audit.StarHost
