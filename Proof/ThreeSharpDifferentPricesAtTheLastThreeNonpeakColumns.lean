import AllLegalPricesOnTheSameHistoryWithoutASecondHighestColumn
namespace JSP452Audit.StarHost

theorem three_nonpeak_taxes (Z N r x y:ℕ) (fit:11*N≤24*Z) (a:3≤x) (b:3≤y) (total:10≤x+y) :
    let J := actualCoordinateLoss Z N r x y
    64*J≤46*Z ∧ (4≤x → 4≤y → 11≤x+y → 64*J≤40*Z) ∧
      (5≤x → 5≤y → 12≤x+y → 64*J≤36*Z) := by
  intro J
  constructor
  · by_cases one:x=3
    · have bound := bounded_point_tax_ratio Z N r x y 3 7 (by decide) (by decide) a (by omega)
      change 31*J≤10*N at bound;omega
    by_cases two:y=3
    · have bound := bounded_point_tax_ratio Z N r x y 7 3 (by decide) (by decide) (by omega) b
      change 31*J≤10*N at bound;omega
    rcases (show 5≤x ∨ 5≤y by omega) with l|r'
    · have bound := bounded_point_tax_ratio Z N r x y 5 4 (by decide) (by decide) l (by omega)
      change 29*J≤9*N at bound;omega
    · have bound := bounded_point_tax_ratio Z N r x y 4 5 (by decide) (by decide) (by omega) r'
      change 29*J≤9*N at bound;omega
  constructor
  · intro xx yy high
    by_cases one:x=4
    · have bound := bounded_point_tax_ratio Z N r x y 4 7 (by decide) (by decide) xx (by omega)
      change 39*J≤11*N at bound;omega
    by_cases two:y=4
    · have bound := bounded_point_tax_ratio Z N r x y 7 4 (by decide) (by decide) (by omega) yy
      change 39*J≤11*N at bound;omega
    have bound := bounded_point_tax_ratio Z N r x y 5 5 (by decide) (by decide) (by omega) (by omega)
    change 35*J≤10*N at bound;omega
  · intro xx yy high
    by_cases one:x=5
    · have bound := bounded_point_tax_ratio Z N r x y 5 7 (by decide) (by decide) xx (by omega)
      change 47*J≤12*N at bound;omega
    by_cases two:y=5
    · have bound := bounded_point_tax_ratio Z N r x y 7 5 (by decide) (by decide) (by omega) yy
      change 47*J≤12*N at bound;omega
    have bound := bounded_point_tax_ratio Z N r x y 6 6 (by decide) (by decide) (by omega) (by omega)
    change 48*J≤12*N at bound;omega

#print axioms three_nonpeak_taxes
end JSP452Audit.StarHost
