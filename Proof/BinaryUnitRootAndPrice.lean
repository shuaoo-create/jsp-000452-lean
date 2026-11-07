import FullBinaryGeneralProfile
namespace JSP452Audit.StarHost

/-- Combine the same root shortfall bound from the component slots and
from the degrees of the roots. -/
theorem binary_unit_root_credit (D a ρ V ζ : ℤ) (degree : 4≤D) (ha : 0≤a) (hz : 0≤ζ)
    (slots : ζ≤D*(V-ρ)) (roots : ζ≤D*a) :
    ρ≤V ∧ ζ≤2*(D-2)*(V-ρ) ∧ ζ≤2*(D-3)*(a+V-ρ) := by
  have gap : ρ≤V := by
    by_contra! bad
    have neg := mul_neg_of_pos_of_neg (show 0<D by omega) (show V-ρ<0 by omega)
    omega
  have pos := mul_nonneg (show 0≤D-4 by omega) (show 0≤V-ρ by omega)
  have total := mul_nonneg (show 0≤3*D-12 by omega) (show 0≤a+V-ρ by omega)
  exact ⟨gap,by nlinarith only [slots,pos],by nlinarith only [slots,roots,total]⟩

/-- Signed arithmetic for the unit exterior. Both options for the
width at height two use the same actual exterior edge count. -/
theorem binary_unit_signed_payment (s t r D a μ S N NB E e eB P A F B k h ρ ζ β w : ℤ)
    (degree : 5≤D) (ha : 0≤a) (hr : 0≤r) (hz : 0≤ζ) (hb : 0≤β) (rho : 0≤ρ) (full : 1≤P) (three : 0≤F)
    (length : s=S+μ) (rank : N≤NB+a+μ) (exterior : 2*ρ≤S)
    (width : h≤ρ) (edge : 2*e+ζ=2*D*(a+μ)+D*ρ+β+2*eB)
    (slot : D*ρ+ζ+D*A≤D*μ) (root : ζ≤D*a) (volume : μ≤3*(μ-A)+a+ρ)
    (peak : P+B=h+r+1) (limit : k+2+r=A+B)
    (area : E≤N+w+(k+1)+(D-3)*k+h)
    (over : F+t<A+B) (winner : w+1+r=A+t ∨ w+1+r=s+B)
    (paid : NB+S+B≤eB+1+r+a) : E≤e := by
  let V := μ-A
  have diff : ζ≤D*(V-ρ) := by dsimp [V];nlinarith only [slot]
  obtain ⟨vlarge,credB,credR⟩ := binary_unit_root_credit D a ρ V ζ (by omega) (by omega) hz diff root
  have key : k=A+h-P-1 := by omega
  rw [key] at area
  have eqμ : μ=A+V := by dsimp [V];ring
  have hcredit := mul_nonneg (show 0≤D-2 by omega) (show 0≤ρ-h by omega)
  have pcredit := mul_nonneg (show 0≤D-2 by omega) (show 0≤P by omega)
  have rcredit := mul_nonneg (show 0≤D-2 by omega) rho
  have low := mul_nonneg (show 0≤D-5 by omega) rho
  have acredit := mul_nonneg (show 0≤D-2 by omega) ha
  have posD : 0≤D-3 := by omega
  have vol : μ≤3*V+a+ρ := volume
  rw [eqμ] at edge
  rcases winner with red|blue
  · nlinarith only [red,peak,area,rank,edge,paid,over,eqμ,vol,credR,hcredit,pcredit,exterior,width,hr,hb,three,low,posD,rho,degree]
  · nlinarith only [blue,peak,area,rank,edge,paid,eqμ,length,credB,hcredit,pcredit,rcredit,acredit,width,hb,posD]

#print axioms binary_unit_root_credit
#print axioms binary_unit_signed_payment
end JSP452Audit.StarHost