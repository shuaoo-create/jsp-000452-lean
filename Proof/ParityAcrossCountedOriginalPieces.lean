import EvenOrderOfClosedFullRegion
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem counted_piece_parity_sum {X:Type u} [Finite X] (G:SimpleGraph X) (a b:ℕ) (oa:Odd a)
    (S T:Set X) :
    let A := S∪T
    let B := uniformOddPieces G a b S T
    let J := regionCore G A B
    ∃m:ℕ,J.ncard+crossCount G J T=2*m+B.ncard := by
  classical
  intro A B J
  let _ := Fintype.ofFinite B
  have parity (C:↥B) := uniform_member_odd_size_boundary G a b oa S T C.val C.property
  choose k hk using parity
  have sum := Finset.sum_congr (s₁:=(Finset.univ:Finset B)) rfl (fun c _ => hk c)
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,
    Nat.mul_one,←Nat.card_eq_fintype_card] at sum
  have size := core_order_sum G A B
  have cross := selected_cut_cross_sum G A B T
  change J.ncard=∑c:↥B,Nat.card c.val.supp at size
  change crossCount G J T=∑c:↥B,crossCount G (cutPieceSet G A c.val) T at cross
  refine ⟨∑c:↥B,k c,?_⟩
  rw [size,cross];exact sum

theorem closed_cut_target_even_incidence {X:Type u} [Finite X] (G:SimpleGraph X) (p:ℕ)
    (S T J:Set X) (dis:Disjoint S T) (off:J⊆(S∪T)ᶜ)
    (zero:crossCount G (S∪T∪J)ᶜ (S∪T)=0) (full:∀x∈T,Nat.card (G.neighborSet x)=2*p) :
    Even (crossCount G J T+crossCount G T S) := by
  let A := S∪T
  let O := Aᶜ
  let U := A∪J
  have so : Disjoint S O := disjoint_compl_right.mono_left Set.subset_union_left
  have to' : Disjoint T O := disjoint_compl_right.mono_left Set.subset_union_right
  have complete : T∪S∪O=Set.univ := by rw [Set.union_comm T S];exact Set.union_compl_self _
  have hand := partition_handshake G T S O dis.symm to' so complete
  rw [degree_sum_full G T (2*p) full] at hand
  have split : J∪Uᶜ=O := by
    ext x;constructor
    · rintro (j|out);exact off j;exact fun a => out (Or.inl a)
    · intro h;by_cases j:x∈J;exact Or.inl j;exact Or.inr (fun aj => aj.elim h j)
  have apart : Disjoint J Uᶜ := disjoint_compl_right.mono_left Set.subset_union_right
  have no : crossCount G T Uᶜ=0 := crossCount_of_no_edges G T Uᶜ (fun x hx y hy e =>
    no_edge_when_port_zero G zero hy (Or.inr hx) e.symm)
  have total := cut_cross_union_right G T J Uᶜ apart
  rw [split,no,Nat.add_zero,crossCount_swap G T J] at total
  rw [total,Nat.mul_assoc] at hand
  refine ⟨p*T.ncard-(G.induce T).edgeSet.ncard,?_⟩
  omega

#print axioms counted_piece_parity_sum
#print axioms closed_cut_target_even_incidence
end JSP452Audit.StarHost
