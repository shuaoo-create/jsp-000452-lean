import QuarticFullBinaryProfile
namespace JSP452Audit.StarHost

/-- The possible negative root contribution at four is at most a+1.
Use the degree cap for at most two roots and the genuine cubic/quartic
selection budget otherwise. -/
theorem four_root_lower_charge (a h ρ ζ β : ℕ) (one : 1≤h) (width : h≤ρ)
    (root : 4*ρ+ζ≤2*h+10) (degree : ζ≤4*a) : ζ+2*h≤4*ρ+β+2*a+2 := by
  by_cases small : a≤2 <;> omega

theorem four_binary_retained_pays (s t r a μ S N NB E e eB P A B c h ρ ζ β d w wB vB : ℕ)
    (length : s=S+μ) (rank : N≤NB+(a+μ)) (mu : 0<μ)
    (deficit : ρ+1≤d) (width : h≤ρ) (inner : t+d≤μ+1)
    (edge : 2*e+ζ=8*(a+μ)+4*ρ+β+2*eB) (root : ζ+2*h≤4*ρ+β+2*a+2)
    (peak : P+B=h+r+1) (bpos : 0<B)
    (area : E≤N+w+(A+B-1-r)+(P+t-1-r)+h) (winner : w=A+t-1-r ∨ w=s+B-1-r)
    (fit : A≤μ+c) (red : c+t-1-(r+a)≤wB) (blue : S+B-1-(r+a)≤wB)
    (mix : c+B-1-(r+a)≤vB) (paid : NB+wB+vB≤eB) : E≤e := by
  have four : P+t-1-r+a+1≤a+μ := by omega
  rcases winner with x|y <;> omega

theorem four_binary_unit_pays (s t r a μ S N NB E e eB P A F B h ρ ζ β d w : ℕ)
    (length : s=S+μ) (rank : N≤NB+(a+μ)) (deficit : ρ+1≤d) (width : h≤ρ) (small : ρ≤5)
    (inner : t+d≤μ+1) (ext : a+r+2*d≤S) (before : r<t) (bpos : 0<B)
    (edge : 2*e+ζ=8*(a+μ)+4*ρ+β+2*eB) (root : ζ+2*h≤4*ρ+β+2*a+2)
    (peak : P+B=h+r+1) (ppos : 0<P) (order : P≤F)
    (area : E≤N+w+(A+B-1-r)+(P+t-1-r)+h) (winner : w=A+t-1-r ∨ w=s+B-1-r)
    (fit : A≤μ) (slots : 3*A≤2*μ+a+ρ) (over : F+t<A+B)
    (paid : NB+(S+B-1-(r+a))≤eB) : E≤e := by
  rcases winner with x|y <;> omega

#print axioms four_root_lower_charge
#print axioms four_binary_retained_pays
#print axioms four_binary_unit_pays
end JSP452Audit.StarHost
