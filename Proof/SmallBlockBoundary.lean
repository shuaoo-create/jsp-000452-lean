import UnifiedNoException
import ZeroCutDegree
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- A missing internal edge increases the boundary count by exactly two
relative to the complete graph on the same region. -/
theorem small_region_boundary_missing (Q : SimpleGraph X) (B : Set X) (D : ℕ)
    (reg : ∀x∈B,Nat.card (Q.neighborSet x)=D) (small : B.ncard≤D+1) :
    crossCount Q B Bᶜ = B.ncard*(D+1-B.ncard)+2*(Q.induce B)ᶜ.edgeSet.ncard := by
  classical
  let _ := Fintype.ofFinite B
  let H := Q.induce B
  have count : Fintype.card B=B.ncard := by rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have per (x : B) : (Q.neighborSet x.val∩Bᶜ).ncard=(D+1-B.ncard)+Hᶜ.degree x := by
    have full := reg x.val x.property
    obtain eq := Set.ncard_sdiff_add_ncard_of_subset (show Q.neighborSet x.val∩B⊆Q.neighborSet x.val from Set.inter_subset_left)
    have out : Q.neighborSet x.val \ (Q.neighborSet x.val∩B)=Q.neighborSet x.val∩Bᶜ := by
      ext v;simp only [Set.mem_sdiff,Set.mem_inter_iff,Set.mem_compl_iff];tauto
    rw [out,←induced_degree_intersection,←Nat.card_coe_set_eq (s:=Q.neighborSet x.val)] at eq
    have inside : Nat.card (H.neighborSet x)=H.degree x := by rw [Nat.card_eq_fintype_card,H.card_neighborSet_eq_degree]
    change (Q.neighborSet x.val∩Bᶜ).ncard+Nat.card (H.neighborSet x)=Nat.card (Q.neighborSet x.val) at eq
    rw [inside,full] at eq
    have room := H.degree_lt_card_verts x
    rw [H.degree_compl,count]
    omega
  rw [crossCount_eq_neighbor_sum]
  simp_rw [per]
  rw [Finset.sum_add_distrib,Hᶜ.sum_degrees_eq_twice_card_edges,Finset.sum_const,Finset.card_univ,smul_eq_mul,
    count,←Hᶜ.card_edgeSet,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]

/-- When the order is odd and the boundary has size at most twice D, small
blocks are triangles at D=6 or size D−1 with at most one missing edge. -/
theorem low_boundary_small_region (Q : SimpleGraph X) (B : Set X) (D : ℕ)
    (large : 6≤D) (evenD : Even D) (odd : Odd B.ncard) (lo : 3≤B.ncard)
    (hi : B.ncard≤D-1) (reg : ∀x∈B,Nat.card (Q.neighborSet x)=D)
    (budget : crossCount Q B Bᶜ≤2*D) :
    (D=6 ∧ B.ncard=3 ∧ (Q.induce B)ᶜ.edgeSet.ncard=0) ∨
      (B.ncard=D-1 ∧ (Q.induce B)ᶜ.edgeSet.ncard≤1) := by
  let u:=B.ncard
  let k:=(Q.induce B)ᶜ.edgeSet.ncard
  have eq := small_region_boundary_missing Q B D reg (by omega)
  change crossCount Q B Bᶜ=u*(D+1-u)+2*k at eq
  have low : 3≤u := lo
  have high : u≤D-1 := hi
  by_cases three : u=3
  · left
    rw [three] at eq
    have sub : D+1-3=D-2 := by omega
    rw [sub] at eq
    exact ⟨by omega,three,by omega⟩
  · have parity := Nat.odd_iff.mp odd
    change u%2=1 at parity
    obtain ⟨d,hd⟩ := evenD
    have five : 5≤u := by omega
    have top : u=D-1 := by
      by_contra short
      have diff : D-u≥3 := by omega
      have times := Nat.mul_le_mul_right (D-u-1) (show 3≤u-2 by omega)
      have nonneg := Nat.mul_le_mul_left (u-2) (show 2≤D-u-1 by omega)
      have repr : D=u+(D-u) := by omega
      have sub : D+1-u=D-u+1 := by omega
      rw [sub,Nat.mul_add,Nat.mul_one] at eq
      generalize hq : D-u=q at diff times nonneg eq repr
      have mul : u*(q-1)=(u-2)*(q-1)+2*(q-1) := by
        rw [←Nat.add_mul,show u-2+2=u by omega]
      have prod : u*q=u*(q-1)+u := by rw [←Nat.mul_succ,show (q-1).succ=q by omega]
      omega
    right
    have gap : D+1-u=2 := by omega
    rw [gap] at eq
    exact ⟨top,by omega⟩

#print axioms small_region_boundary_missing
#print axioms low_boundary_small_region
end JSP452Audit.StarHost
