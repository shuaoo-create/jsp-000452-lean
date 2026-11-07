import FullUnitPaidMiddleSum
namespace JSP452Audit.StarHost

theorem large_gap_shortfall_credit (D c a V ρ ζ : ℤ) (degree : 1≤D) (gap : D≤4*(c-1)) (az : 0≤a)
    (rz : 0≤ρ) (zz : 0≤ζ) (slots : ζ≤D*(V-ρ)) (cap : ζ≤D*a) :
    ρ≤V ∧ ζ≤2*(c-1)*(a+V) := by
  have large : ρ≤V := by
    by_contra! small
    have neg := mul_neg_of_pos_of_neg (show 0<D by omega) (show V-ρ<0 by omega)
    omega
  have mult := mul_nonneg (show 0≤4*(c-1)-D by omega) (show 0≤a+V-ρ by omega)
  have adjust := mul_nonneg (show 0≤c-1 by omega) rz
  exact ⟨large,by nlinarith only [slots,cap,mult,adjust]⟩

theorem unit_gap_signed_payment (D c a μ N NB E e eB h ρ ζ β V S B t w u C U : ℤ)
    (degree : 6≤D) (gap : D≤4*(c-1)) (az : 0≤a) (rz : 0≤ρ) (zz : 0≤ζ) (bz : 0≤β)
    (slot : ζ≤D*(V-ρ)) (cap : ζ≤D*a) (volume : μ≤3*V+a+ρ)
    (width : h≤ρ) (outside : ρ≤S) (over : t+V≤μ+B)
    (edge : 2*e+ζ=2*D*(a+μ)+D*ρ+β+2*eB) (rank : N≤NB+a+μ)
    (area : E≤N+w+C+h) (middle : C+c*(V+a+1)≤(D-2)*(a+μ)+U) (ext : NB+u+U≤eB)
    (winner : w≤a+μ+u ∨ w+S+B+V≤a+μ+u+t) : E≤e := by
  obtain ⟨large,credit⟩ := large_gap_shortfall_credit D c a V ρ ζ (by omega) gap az rz zz slot cap
  have positive := mul_nonneg (show 0≤D-2 by omega) rz
  rcases winner with blue|red
  · nlinarith only [credit,positive,edge,rank,area,middle,ext,blue,width,bz,large,az,rz,gap,degree]
  · nlinarith only [credit,positive,edge,rank,area,middle,ext,red,volume,outside,over,width,bz,gap,degree]

#print axioms large_gap_shortfall_credit
#print axioms unit_gap_signed_payment
end JSP452Audit.StarHost