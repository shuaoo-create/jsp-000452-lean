import PartitionHandshake
import RegionDegreeSum

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

omit [Finite X] in
private theorem cross_at_singleton (T : SimpleGraph X) (w : X) (A : Set X) :
    crossCount T {w} A = (T.neighborSet w ∩ A).ncard := by
  classical
  let e : {p : (↥({w} : Set X) × ↥A) // T.Adj p.1.val p.2.val} ≃ ↥(T.neighborSet w ∩ A) :=
    { toFun := fun p => ⟨p.val.2.val, by
        have eq : p.val.1.val = w := p.val.1.property
        refine ⟨?_,p.val.2.property⟩
        change T.Adj w p.val.2.val
        exact (congrArg (fun z : X => T.Adj z p.val.2.val) eq).mp p.property⟩
      invFun := fun y => ⟨(⟨w,rfl⟩,⟨y.val,y.property.2⟩),y.property.1⟩
      left_inv := by rintro ⟨⟨⟨a,ha⟩,b⟩,e⟩; obtain rfl := Set.mem_singleton_iff.mp ha; rfl
      right_inv := fun _ => rfl }
  exact Nat.card_congr e

/-- In an odd triangle-free regular graph of degree at least two and complementary
degree at least three, the order exceeds twice the degree by at least three. -/
theorem triangle_regular_order (T : SimpleGraph X) (c : ℕ) (odd : Odd (Nat.card X))
    (reg : ∀ x, Nat.card (T.neighborSet x) = c)
    (tri : ∀ x y z, T.Adj x y → T.Adj y z → ¬T.Adj z x)
    (hc : 2≤c) (hcod : 3≤Nat.card X-1-c) : 2*c+3 ≤ Nat.card X := by
  classical
  obtain ⟨par,hpar⟩ := odd
  have ⟨x⟩ : Nonempty X := (Nat.card_pos_iff.mp (by omega : 0 < Nat.card X)).1
  have size (v : X) : (T.neighborSet v).ncard=c := reg v
  obtain ⟨y,xy⟩ := (Set.ncard_pos (s := T.neighborSet x)).mp (by rw [size]; omega)
  let A := T.neighborSet x
  let B := T.neighborSet y
  have ab : Disjoint A B := Set.disjoint_left.mpr fun z xz yz => tri x y z xy yz xz.symm
  have independent (v : X) : ∀ a∈T.neighborSet v, ∀ b∈T.neighborSet v, ¬T.Adj a b :=
    fun a ha b hb edge => tri v a b ha edge hb.symm
  have ca : A.ncard=c := size x
  have cb : B.ncard=c := size y
  have count := Set.ncard_add_ncard_compl (A∪B)
  rw [Set.ncard_union_eq ab,ca,cb] at count
  by_contra! small
  have one : (A∪B)ᶜ.ncard=1 := by omega
  obtain ⟨w,only⟩ := Set.ncard_eq_one.mp one
  have outside : w∉A∪B := by change w∈(A∪B)ᶜ; rw [only]; rfl
  have aw : Disjoint A ({w} : Set X) := Set.disjoint_left.mpr (by
    rintro _ h eq; obtain rfl := Set.mem_singleton_iff.mp eq; exact outside (Or.inl h))
  have bw : Disjoint B ({w} : Set X) := Set.disjoint_left.mpr (by
    rintro _ h eq; obtain rfl := Set.mem_singleton_iff.mp eq; exact outside (Or.inr h))
  have cover : A∪B∪{w}=Set.univ := by rw [← only,Set.union_compl_self]
  have hA := partition_handshake T A B {w} ab aw bw cover
  have hB := partition_handshake T B A {w} ab.symm bw aw (by rwa [Set.union_comm B A])
  rw [degree_sum_full T A c (fun a _ => reg a),ca,← crossCount_self,
    crossCount_of_no_edges T A A (independent x),crossCount_swap T A {w},cross_at_singleton] at hA
  rw [degree_sum_full T B c (fun a _ => reg a),cb,← crossCount_self,
    crossCount_of_no_edges T B B (independent y),crossCount_swap T B A,
    crossCount_swap T B {w},cross_at_singleton] at hB
  have balance : (T.neighborSet w ∩ A).ncard = (T.neighborSet w ∩ B).ncard := by omega
  have union : (T.neighborSet w ∩ A) ∪ (T.neighborSet w ∩ B) = T.neighborSet w := by
    rw [← Set.inter_union_distrib_left]
    apply Set.inter_eq_left.mpr
    intro v hv
    by_contra out
    have eq : v∈({w}:Set X) := only ▸ out
    exact hv.ne (Set.mem_singleton_iff.mp eq).symm
  have both := congrArg Set.ncard union
  rw [Set.ncard_union_eq (ab.mono Set.inter_subset_right Set.inter_subset_right), size] at both
  obtain ⟨a,wa,ha⟩ := (Set.ncard_pos (s := T.neighborSet w ∩ A)).mp (by omega)
  let N := T.neighborSet a \ {w}
  have keep : N ⊆ B := by
    rintro v ⟨av,diff⟩
    by_contra bv
    have out : v∉A∪B := by
      rintro (inA|inB)
      · exact independent x a ha v inA av
      · exact bv inB
    exact diff (only ▸ out)
  have wn : w∈T.neighborSet a := wa.symm
  have cn : N.ncard=c-1 := by
    rw [Set.ncard_sdiff' (Set.singleton_subset_iff.mpr wn),Set.ncard_singleton,size]
  have sep : Disjoint N (T.neighborSet w ∩ B) := Set.disjoint_left.mpr fun v hv h =>
    tri w a v wa hv.1 h.1.symm
  have le := Set.ncard_le_ncard (Set.union_subset keep (Set.inter_subset_right (s := T.neighborSet w) (t := B)))
  rw [Set.ncard_union_eq sep,cn,cb] at le
  omega

#print axioms triangle_regular_order
end JSP452Audit.StarHost
