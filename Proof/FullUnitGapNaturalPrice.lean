import FullUnitUniformGapPrice
namespace JSP452Audit.StarHost

theorem unit_gap_natural_payment (s r D c a μ N NB E e eB h ρ ζ β V A S B t w u C U : ℕ)
    (degree : 6≤D) (gap : D≤4*(c-1)) (fit : V+A=μ) (len : s=S+μ)
    (slot : D*ρ+ζ+D*A≤D*μ) (cap : ζ≤D*a) (vol : μ≤3*V+a+ρ)
    (width : h≤ρ) (outside : ρ≤S) (over : t<A+B) (before : r<t)
    (edge : 2*e+ζ=2*D*(a+μ)+D*ρ+β+2*eB) (rank : N≤NB+a+μ)
    (area : E≤N+w+C+h) (middle : C+c*(V+a+1)≤(D-2)*(a+μ)+U) (ext : NB+u+U≤eB)
    (winner : w=A+t-1-r ∨ w=s+B-1-r) (low : S+B-1-(r+a)≤u) : E≤e := by
  have c1 : c-1+1=c := by omega
  have k2 : D-2+2=D := by omega
  have ec : ((c-1:ℕ):ℤ)+1=c := by exact_mod_cast c1
  have ek : ((D-2:ℕ):ℤ)+2=D := by exact_mod_cast k2
  have gi : (D:ℤ)≤4*((c-1:ℕ):ℤ) := by exact_mod_cast gap
  rw [show ((c-1:ℕ):ℤ)=(c:ℤ)-1 by omega] at gi
  have mi : (C:ℤ)+(c:ℤ)*(V+a+1)≤((D-2:ℕ):ℤ)*(a+μ)+U := by exact_mod_cast middle
  rw [show ((D-2:ℕ):ℤ)=(D:ℤ)-2 by omega] at mi
  have si : (D:ℤ)*ρ+ζ+(D:ℤ)*A≤(D:ℤ)*μ := by exact_mod_cast slot
  have eqμ : (μ:ℤ)=V+A := by exact_mod_cast fit.symm
  rw [eqμ] at si
  have bound : t+V≤μ+B := by omega
  have win : w≤a+μ+u ∨ w+S+B+V≤a+μ+u+t := by rcases winner with a|b <;> omega
  have wi : (w:ℤ)≤a+μ+u ∨ (w:ℤ)+S+B+V≤a+μ+u+t := by
    rcases win with a|b
    · left;exact_mod_cast a
    · right;exact_mod_cast b
  have result := unit_gap_signed_payment D c a μ N NB E e eB h ρ ζ β V S B t w u C U (by exact_mod_cast degree)
    gi (by positivity) (by positivity) (by positivity) (by positivity) (by nlinarith only [si]) (by exact_mod_cast cap)
    (by exact_mod_cast vol) (by exact_mod_cast width) (by exact_mod_cast outside) (by exact_mod_cast bound)
    (by exact_mod_cast edge) (by exact_mod_cast rank) (by exact_mod_cast area) mi (by exact_mod_cast ext) wi
  exact_mod_cast result

#print axioms unit_gap_natural_payment
end JSP452Audit.StarHost