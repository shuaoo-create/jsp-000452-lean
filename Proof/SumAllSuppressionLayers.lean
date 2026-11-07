import SevenHighSuppressionPrice
namespace JSP452Audit.StarHost

theorem divide_at_opposing_head (D b : ℕ) (lo : 2≤b) (hi : b<D) (F : ℕ→ℕ) :
    (∑z∈Finset.range (D-2),F (z+3))=(∑z∈Finset.range (b-2),F (z+3))+F (b+1)+
      ∑z∈Finset.range (D-b-1),F (b+2+z) := by
  have eq := Finset.sum_range_add (fun z => F (z+3)) (b-1) (D-b-1)
  rw [show b-1+(D-b-1)=D-2 by omega] at eq
  rw [eq,show b-1=(b-2)+1 by omega,Finset.sum_range_succ]
  simp only [show b-2+3=b+1 by omega,show ∀z:ℕ,b-2+1+z+3=b+2+z by omega]

theorem sum_high_endpoint_prices (D b P ρ h d X q : ℕ) (C Q f : ℕ→ℕ) (lo : 2≤b) (hi : b<D)
    (low : 2*C 2≤Q 2+q) (axes : ∀j,3≤j → j≤b → 2*C j≤Q j+2*f j)
    (border : 2*C (b+1)≤Q (b+1)+2*f (b+1)+2*ρ)
    (higher : ∀j,b+2≤j → j≤D → 2*C j+P≤Q j+2*f j)
    (mass : (∑z∈Finset.range (D-2),f (z+3))≤2*X)
    (balance : q+4*X+2*ρ+2*h+2*d≤(D-b-1)*P+D*ρ) :
    2*(∑z∈Finset.range (D-1),C (z+2))+2*h+2*d≤(∑z∈Finset.range (D-1),Q (z+2))+D*ρ := by
  have lowS := Finset.sum_le_sum (s:=Finset.range (b-2)) (fun z mem =>
    axes (z+3) (by omega) (by have := Finset.mem_range.mp mem;omega))
  have highS := Finset.sum_le_sum (s:=Finset.range (D-b-1)) (fun z mem =>
    higher (b+2+z) (by omega) (by have := Finset.mem_range.mp mem;omega))
  simp only [Finset.sum_add_distrib,←Finset.mul_sum] at lowS highS
  simp at highS
  have peel (F:ℕ→ℕ) : (∑z∈Finset.range (D-1),F (z+2))=F 2+(∑z∈Finset.range (D-2),F (z+3)) := by
    rw [show D-1=(D-2)+1 by omega,Finset.sum_range_succ'];simp [Nat.add_comm]
  rw [peel C,peel Q,divide_at_opposing_head D b lo hi C,divide_at_opposing_head D b lo hi Q]
  rw [divide_at_opposing_head D b lo hi f] at mass
  omega

#print axioms divide_at_opposing_head
#print axioms sum_high_endpoint_prices
end JSP452Audit.StarHost