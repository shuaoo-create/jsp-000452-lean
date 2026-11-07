import OriginalSplitBudget
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X J : Type*} [Finite X] [Fintype J]

private theorem clique_price_id (D n : ℕ) (lo : 2≤n) (hi : n≤D-1) :
    n*(D+1-n)=2*D-2+(n-2)*(D-1-n) := by
  let a := n-2
  let b := D-1-n
  have size : n=a+2 := by dsimp [a];omega
  have gap : D+1-n=b+2 := by dsimp [b];omega
  have degree : D=a+b+3 := by dsimp [a,b];omega
  change n*(D+1-n)=2*D-2+a*b
  rw [gap,size,Nat.add_mul,Nat.mul_add]
  omega

/-- If one of the remaining cliques has at least three vertices, the root
budget forces that clique to have size D−1 and every other part to be a singleton. -/
theorem split_clique_sizes_from_four (G : SimpleGraph X) (C : J→Set X) (R : Set X) (D : ℕ)
    (four : 4≤D) (card : R.ncard=Fintype.card J+1)
    (apart : ∀ i j, i≠j → Disjoint (C i) (C j)) (outside : ∀ i, C i⊆Rᶜ)
    (closed : ∀ i a, a∈C i → ∀ b, G.Adj a b → b∉C i → b∈R)
    (reg : ∀ x, Nat.card (G.neighborSet x)=D)
    (internal : ∃ a∈R, ∃ b∈R, G.Adj a b)
    (cl : ∀i, G.IsClique (C i)) (sizes : ∀i, 1≤(C i).ncard ∧ (C i).ncard≤D-1)
    (j : J) (big : 3≤(C j).ncard) :
    (C j).ncard=D-1 ∧ ∀i, i≠j → (C i).ncard=1 := by
  classical
  let f (i:J) := crossCount G (C i) (C i)ᶜ
  let g (i:J) := D+(if i=j then D-2 else 0)
  have cost (i:J) : f i=(C i).ncard*(D+1-(C i).ncard) :=
    clique_boundary_count G (C i) D (cl i) (fun x _ => reg x)
  have cap := split_roots_cut_cap G C R D apart outside closed reg internal
  rw [card,Nat.add_mul,one_mul] at cap
  change (∑i,f i)+2≤Fintype.card J*D+D at cap
  have le (i:J) : g i≤f i := by
    by_cases eq : i=j
    · subst i
      have idn := clique_price_id D (C j).ncard (by omega) (sizes j).2
      simp [g]; rw [cost];omega
    · simp only [g,if_neg eq,add_zero]
      exact clique_boundary_at_least_degree G (C i) D (cl i) (fun x _ => reg x)
        (sizes i).1 (by have h:=(sizes i).2; omega)
  have total : (∑i,g i)=Fintype.card J*D+(D-2) := by
    simp [g,Finset.sum_add_distrib]
  have tight (i:J) : f i=g i := by
    by_contra diff
    have lt : (∑i,g i)<∑i,f i := Finset.sum_lt_sum (fun t _ => le t)
      ⟨i,Finset.mem_univ _,lt_of_le_of_ne (le i) (Ne.symm diff)⟩
    omega
  constructor
  · have payment := tight j
    simp [g] at payment
    rw [cost,clique_price_id D _ (by omega) (sizes j).2] at payment
    have zero : ((C j).ncard-2)*(D-1-(C j).ncard)=0 := by omega
    rcases Nat.mul_eq_zero.mp zero with z|z
    · omega
    · have h := (sizes j).2; omega
  · intro i diff
    by_contra ne
    have two : 2≤(C i).ncard := by have h:=(sizes i).1; omega
    have payment := tight i
    simp only [g,if_neg diff,add_zero] at payment
    rw [cost,clique_price_id D _ two (sizes i).2] at payment
    omega

/-- Pull the separated cliques back to the original labels and use the edge
from the new pivot to the old independent set in the root degree budget. -/
theorem original_split_clique_sizes_from_four (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (x : ↥(Iᶜ : Set X)) (F : J → Set ↥(Iᶜ : Set X)) (card : I.ncard=Fintype.card J)
    (apart : ∀i j,i≠j → Disjoint (F i) (F j)) (off : ∀i,x∉F i)
    (cover : ∀v,v≠x → ∃i,v∈F i) (cl : ∀i,(Q.induce Iᶜ).IsClique (F i))
    (sep : ∀i j,i≠j → ∀a∈F i,∀b∈F j,¬ (Q.induce Iᶜ).Adj a b)
    (sizes : ∀ i, 1≤(F i).ncard ∧ (F i).ncard≤D-1)
    (j : J) (big : 3≤(F j).ncard) :
    (F j).ncard=D-1 ∧ ∀i,i≠j → (F i).ncard=1 := by
  classical
  let R := insert x.val I
  let C (i:J) : Set X := Subtype.val '' F i
  have eq (i:J) : (C i).ncard=(F i).ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have out (i:J) : C i⊆Rᶜ := by
    rintro _ ⟨v,hv,rfl⟩ h
    rcases Set.mem_insert_iff.mp h with e|e
    · exact off i ((Subtype.ext e : v=x) ▸ hv)
    · exact v.property e
  have external (i:J) (a:X) (ha:a∈C i) (b:X) (edge:Q.Adj a b) (away:b∉C i) : b∈R := by
    by_contra outside
    obtain ⟨v,hv,rfl⟩ := ha
    let t : ↥(Iᶜ : Set X) := ⟨b,fun ib => outside (Set.mem_insert_of_mem _ ib)⟩
    have tx : t≠x := fun same => outside (Set.mem_insert_iff.mpr (Or.inl (congrArg Subtype.val same)))
    obtain ⟨k,hk⟩ := cover t tx
    exact sep i k (fun e => away ⟨t,e.symm ▸ hk,rfl⟩) v hv t hk edge
  have clique (i:J) : Q.IsClique (C i) := by
    rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ diff
    exact cl i hu hv (fun h => diff (congrArg Subtype.val h))
  have internal : ∃a∈R,∃b∈R,Q.Adj a b := by
    obtain ⟨z,hz,edge⟩ := largest_independent_dominates Q I ind largest x.val x.property
    exact ⟨x.val,Set.mem_insert _ _,z,Set.mem_insert_of_mem _ hz,edge⟩
  have rootCard : R.ncard=Fintype.card J+1 := by
    rw [show R=insert x.val I from rfl,Set.ncard_insert_of_notMem x.property,card]
  have result := split_clique_sizes_from_four Q C R D four rootCard
    (fun i k ne => Set.disjoint_image_of_injective Subtype.val_injective (apart i k ne))
    out external reg internal clique (fun i => by rw [eq];exact sizes i) j (by rw [eq];exact big)
  exact ⟨(eq j).symm.trans result.1,fun i ne => (eq i).symm.trans (result.2 i ne)⟩

#print axioms original_split_clique_sizes_from_four
end JSP452Audit.StarHost
