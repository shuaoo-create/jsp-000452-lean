import LowPairAndTopOnActualGraph
namespace JSP452Audit.StarHost

theorem split_three_interior_layers (D : ℕ) (hi : 6≤D) (f : ℕ→ℕ) :
    (∑q∈Finset.range (D-1),f (q+2))=
      f 2+f 3+(∑q∈Finset.range (D-4),f (q+4))+f D := by
  rw [show D-1=(2+(D-4))+1 by omega,Finset.sum_range_succ,Finset.sum_range_add]
  rw [show 2+(D-4)+2=D by omega]
  have mid : (∑x∈Finset.range (D-4),f (2+x+2))=∑x∈Finset.range (D-4),f (x+4) := by
    exact Finset.sum_congr rfl (fun x _ => congrArg f (by omega))
  rw [mid];simp [Finset.sum_range_succ]

theorem fold_low_top_boundary (D b d ρ X : ℕ) (L C A : ℕ→ℕ) (deg : 6≤D)
    (triple : 2*L 2+2*L 3+2*L D+2*X+2*d≤C 2+C 3+C D+A 2+A 3+2*ρ)
    (others : ∀j,4≤j → j<D → 2*L j≤C j+A j+(if j=b+1 then 2*ρ else 0))
    (axes : (∑q∈Finset.range (D-1),A (q+2))≤2*X) :
    2*(∑q∈Finset.range (D-1),L (q+2))+2*d≤(∑q∈Finset.range (D-1),C (q+2))+4*ρ := by
  classical
  have per (z:ℕ) (mem:z∈Finset.range (D-4)) := others (z+4) (by omega) (by have := Finset.mem_range.mp mem;omega)
  have sum := Finset.sum_le_sum (s:=Finset.range (D-4)) per
  rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_add_distrib] at sum
  have allowance : (∑z∈Finset.range (D-4),if z+4=b+1 then 2*ρ else 0)≤2*ρ := by
    calc
      _ ≤ ∑z∈Finset.range (D-4),if z=b-3 then 2*ρ else 0 := by
        apply Finset.sum_le_sum
        intro z _;split_ifs <;> omega
      _ ≤ _ := by rw [Finset.sum_ite_eq'];split_ifs <;> omega
  rw [split_three_interior_layers D deg L,split_three_interior_layers D deg C]
  rw [split_three_interior_layers D deg A] at axes
  omega

#print axioms split_three_interior_layers
#print axioms fold_low_top_boundary
end JSP452Audit.StarHost
