import BinaryUnitRootAndPrice
namespace JSP452Audit.StarHost

theorem binary_unit_general_payment (s t r D a μ S N NB E e eB P A F B h ρ ζ β d w : ℕ)
    (degree : 5≤D) (length : s=S+μ) (rank : N≤NB+(a+μ)) (reserve : ρ+1≤d)
    (width : h≤ρ) (outer : a+r+2*d≤S) (before : r<t) (full : 0<P)
    (edge : 2*e+ζ=2*D*(a+μ)+D*ρ+β+2*eB)
    (slot : D*ρ+ζ+D*A≤D*μ) (root : ζ≤D*a) (volume : 3*A≤2*μ+a+ρ)
    (peak : P+B=h+r+1) (over : F+t<A+B)
    (area : E≤N+w+(A+B-1-r)+(D-3)*(A+B-2-r)+h)
    (winner : w=A+t-1-r ∨ w=s+B-1-r)
    (paid : NB+(S+B-1-(r+a))≤eB) : E≤e := by
  let k := A+B-2-r
  let c := D-3
  have ck : c+3=D := by dsimp [c];omega
  have eqk : k+2+r=A+B := by dsimp [k];omega
  have area' : E≤N+w+(k+1)+c*k+h := by
    have eqp : A+B-1-r=k+1 := by omega
    rw [eqp] at area;exact area
  have ec : (c:ℤ)+3=(D:ℤ) := by exact_mod_cast ck
  have ea : (E:ℤ)≤N+w+((k:ℤ)+1)+(c:ℤ)*k+h := by exact_mod_cast area'
  rw [show (c:ℤ)=(D:ℤ)-3 by omega] at ea
  have roots : (3:ℤ)*A≤2*(μ:ℤ)+a+ρ := by exact_mod_cast volume
  have wp : w+1+r=A+t ∨ w+1+r=s+B := by rcases winner with x|y <;> omega
  have wf : (w:ℤ)+1+r=(A:ℤ)+t ∨ (w:ℤ)+1+r=(s:ℤ)+B := by
    rcases wp with x|y
    · left;exact_mod_cast x
    · right;exact_mod_cast y
  have rank' : N≤NB+a+μ := by omega
  have outer' : 2*ρ≤S := by omega
  have edgeB : NB+S+B≤eB+1+r+a := by omega
  have pay := binary_unit_signed_payment s t r D a μ S N NB E e eB P A F B k h ρ ζ β w
    (by exact_mod_cast degree) (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (by exact_mod_cast full) (by positivity) (by exact_mod_cast length) (by exact_mod_cast rank')
    (by exact_mod_cast outer') (by exact_mod_cast width) (by exact_mod_cast edge) (by exact_mod_cast slot)
    (by exact_mod_cast root) (by linarith only [roots]) (by exact_mod_cast peak) (by exact_mod_cast eqk)
    ea (by exact_mod_cast over) wf (by exact_mod_cast edgeB)
  exact_mod_cast pay

#print axioms binary_unit_general_payment
end JSP452Audit.StarHost