import QuarticTernaryTrueProfile
namespace JSP452Audit.StarHost

theorem quartic_slot_root_margin (μ A c h ρ ζ β : ℕ) (one : 1≤h) (width : h≤ρ)
    (root : 4*ρ+ζ≤2*h+10) (slot : 4*ρ+ζ+4*A≤4*(μ+c)) :
    ζ+2*h+2*A≤4*ρ+β+2*(μ+c) := by omega

theorem quartic_ternary_retained_pays (s t r a μ S N NB E e eB P F A B Q c h ρ ζ β d w₂ w₃ w₄ b₂ b₃ b₄ : ℕ)
    (length : s=S+μ) (rank : N≤NB+(a+μ)) (mupos : 0<μ) (deficit : ρ+1≤d) (width : h≤ρ)
    (inner : t+d≤μ+1) (edge : 2*e+ζ=8*(a+μ)+4*ρ+β+2*eB)
    (root : ζ+2*h≤4*ρ+β+2*a+2) (slot : ζ+2*h+2*A≤4*ρ+β+2*(μ+c))
    (pc : P≤r+h) (fc : F≤r+h) (area : E=N+w₂+w₃+w₄+h)
    (w2 : w₂=A+t-1-r ∨ w₂=s+B-1-r)
    (w3 : w₃=F+t-1-r ∨ w₃=A+B-1-r ∨ w₃=s+Q-1-r)
    (w4 : w₄≤P+t-1-r ∨ w₄=A+Q-1-r)
    (fit : A≤μ+c) (b2r : c+t-1-(r+a)≤b₂) (b2b : S+B-1-(r+a)≤b₂)
    (b3r : c+B-1-(r+a)≤b₃) (b3b : S+Q-1-(r+a)≤b₃) (b4r : c+Q-1-(r+a)≤b₄)
    (paid : NB+b₂+b₃+b₄≤eB) : E≤e := by
  have second : w₂≤a+μ+b₂ := by rcases w2 with h|h <;> omega
  have third : w₃≤a+μ+b₃ := by rcases w3 with h|h|h <;> omega
  by_cases z : w₄=0
  · omega
  rcases w4 with red|mixed <;> omega

theorem quartic_ternary_unit_pays (s t r a μ S N NB E e eB P F A B Q h ρ ζ β d w₂ w₃ w₄ : ℕ)
    (length : s=S+μ) (rank : N≤NB+(a+μ)) (deficit : ρ+1≤d) (width : h≤ρ)
    (inner : t+d≤μ+1) (ext : a+r+2*d≤S) (before : r<t)
    (edge : 2*e+ζ=8*(a+μ)+4*ρ+β+2*eB) (root : ζ+2*h≤4*ρ+β+2*a+2)
    (boundF : F≤r+h) (boundB : B≤r+ρ) (bpos : 0<B) (qpos : 0<Q) (boundQ : Q≤r)
    (ppos : 0<P) (area : E=N+w₂+w₃+w₄+h) (w2 : w₂=A+t-1-r ∨ w₂=s+B-1-r)
    (w3 : w₃=F+t-1-r ∨ w₃=A+B-1-r ∨ w₃=s+Q-1-r)
    (w4 : w₄≤P+t-1-r ∨ w₄=A+Q-1-r)
    (few : A≤μ) (slots : 3*A≤2*μ+a+ρ) (over : P+t<A+Q)
    (paid : NB+(S+B-1-(r+a))+(S+Q-1-(r+a))≤eB) : E≤e := by
  have third : w₃≤s+Q-1-r := by rcases w3 with h|h|h <;> omega
  have fourth : w₄≤A+Q-1-r := by rcases w4 with h|h <;> omega
  rcases w2 with x|y <;> omega

#print axioms quartic_slot_root_margin
#print axioms quartic_ternary_retained_pays
#print axioms quartic_ternary_unit_pays
end JSP452Audit.StarHost
