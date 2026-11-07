import StrictFullPureHeightRange
namespace JSP452Audit.StarHost

theorem gap_two_four_prices (μ a r d h ρ t S c V q f δ w2 w3 wb wD e2 e3 eb eD : ℕ)
    (width : h≤ρ) (reserve : ρ+1≤d) (qeq : q+t=μ+1) (space : d≤q)
    (original : a+r+2*(d+f)≤t) (outside : a+r+2*d+δ≤S)
    (rankVol : μ+c≤S+V+a+ρ+3*δ) (slotVol : μ≤3*V+a+ρ)
    (pure : μ+S≤f+t) (fit : δ≤V)
    (low : 2*w2+2*δ≤e2 ∨ 2*w2+V≤e2+q)
    (third : 2*w3≤e3+2*q) (top : 2*wD+a+2*q≤eD)
    (boundary : 2*wb+a+2*q≤eb ∨ 2*wb+2*V≤eb+c) :
    2*w2+2*w3+2*wb+2*wD+2*h+2*d≤e2+e3+eb+eD+6*ρ := by
  rcases low with l|l <;> rcases boundary with b|b <;>
    linarith only [width,reserve,qeq,space,original,outside,rankVol,slotVol,pure,fit,l,third,top,b,
      Nat.zero_le a,Nat.zero_le r,Nat.zero_le δ,Nat.zero_le ρ,Nat.zero_le c,Nat.zero_le V]

theorem gap_two_fold_four (D h ρ d : ℕ) (C Q : ℕ→ℕ) (deg : 6≤D)
    (four : 2*C 2+2*C 3+2*C (D-1)+2*C D+2*h+2*d≤Q 2+Q 3+Q (D-1)+Q D+6*ρ)
    (inside : ∀j,4≤j → j≤D-2 → 2*C j≤Q j) :
    2*(∑z∈Finset.range (D-1),C (z+2))+2*h+2*d≤(∑z∈Finset.range (D-1),Q (z+2))+D*ρ := by
  have split (F:ℕ→ℕ) : (∑z∈Finset.range (D-1),F (z+2))=
      F 2+F 3+(∑z∈Finset.range (D-5),F (z+4))+F (D-1)+F D := by
    rw [show D-1=(D-3)+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,
      show D-3=(D-5)+1+1 by omega,Finset.sum_range_succ',Finset.sum_range_succ']
    simp only [Nat.zero_add,show (1:ℕ)+2=3 by decide,show D-5+1+1+1+2=D by omega,show D-5+1+1+2=D-1 by omega]
    simp only [show ∀z:ℕ,z+1+1+2=z+4 by omega]
    omega
  have pay := Finset.sum_le_sum (s:=Finset.range (D-5)) (fun z mem => inside (z+4) (by omega)
    (by have := Finset.mem_range.mp mem;omega))
  rw [←Finset.mul_sum] at pay
  have charge := Nat.mul_le_mul_right ρ deg
  rw [split C,split Q];omega

#print axioms gap_two_four_prices
#print axioms gap_two_fold_four
end JSP452Audit.StarHost