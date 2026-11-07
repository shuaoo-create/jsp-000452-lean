import MajorityPairedTrueHeights
namespace JSP452Audit.StarHost

theorem majority_four_prices (μ a r d h ρ t S c V q f δ w2 w3 wb wD e2 e3 eb eD : ℕ)
    (width : h≤ρ) (reserve : ρ+1≤d) (qeq : q+t=μ+1) (space : d≤q)
    (original : a+r+2*(d+f)≤t) (outside : a+r+2*d+δ≤S)
    (rankVol : μ+c≤S+V+a+ρ+3*δ) (slotVol : μ≤3*V+a+ρ)
    (pure : μ+S≤f+t) (fit : δ≤V)
    (low : 2*w2+2*δ≤e2 ∨ 2*w2+V≤e2+q)
    (third : 2*w3≤e3+2*q) (top : 2*wD+a+2*q≤eD)
    (boundary : 2*wb+a+2*q≤eb+2*h ∨ 2*wb+2*V≤eb+c) :
    2*w2+2*w3+2*wb+2*wD+2*h+2*d≤e2+e3+eb+eD+4*ρ := by
  rcases low with l|l <;> rcases boundary with b|b <;>
    linarith only [width,reserve,qeq,space,original,outside,rankVol,slotVol,pure,fit,l,third,top,b,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le δ,Nat.zero_le ρ,Nat.zero_le c,Nat.zero_le V]

/-- All prices are for a single pair of exterior and erased-core
inventories. The coarser bound q suffices for each even cut. -/
theorem majority_genuine_layer_prices (s t r a μ S A c V q δ l B g f w2 w3 wb wD h
    u2 z2 u3 z3 ub zb uD zD : ℕ)
    (before : r<t) (remain : r<s) (bound : q+t=μ+1) (fit : V+A=μ+c) (len : l+μ=s+δ)
    (rank : s=S+μ) (gcap : g≤r) (low : w2=A+t-1-r ∨ w2=s+B-1-r)
    (third : w3=f+t-1-r) (last : wD≤t-1) (bshape : wb≤t-1+h ∨ wb=A+g-1-r)
    (ared : c+t-1-(r+a)≤u2) (bblue : l+B-1-(r+a)≤u2) (zblue : l+B-1-r≤z2)
    (repair2 : A≤z2+2*q+r) (repair3 : f≤u3+2*q+r+a ∧ f≤z3+2*q+r)
    (mix : c+g-1-(r+a)≤ub) :
    let Q2 := a+2*μ+u2+z2
    let Q3 := a+2*μ+u3+z3
    let Qb := a+2*μ+ub+zb
    let QD := a+2*μ+uD+zD
    (2*w2+2*δ≤Q2 ∨ 2*w2+V≤Q2+q) ∧ 2*w3≤Q3+2*q ∧ 2*wD+a+2*q≤QD ∧
    (2*wb+a+2*q≤Qb+2*h ∨ 2*wb+2*V≤Qb+c) := by
  intro Q2 Q3 Qb QD
  dsimp only [Q2,Q3,Qb,QD]
  refine ⟨?_,by omega,by omega,?_⟩
  · rcases low with rw|bw <;> omega
  · rcases bshape with axis|rect <;> omega


#print axioms majority_four_prices
#print axioms majority_genuine_layer_prices
end JSP452Audit.StarHost