import DetachedPairExactPrices
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem one_excess_label {J : Type*} [Fintype J] (f : J→ℕ)
    (pos : ∀j,1≤f j) (total : ∑j,f j=Fintype.card J+1) :
    ∃z,f z=2 ∧ ∀j,j≠z → f j=1 := by
  classical
  have someBig : ∃z,2≤f z := by
    by_contra! small
    have cap := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => (show f j≤1 by have h:=small j;omega))
    simp only [Finset.sum_const,smul_eq_mul,Finset.card_univ,mul_one] at cap
    omega
  obtain ⟨z,hz⟩ := someBig
  let g (j:J) := 1+(if j=z then 1 else 0)
  have le (j:J) : g j≤f j := by
    by_cases eq:j=z
    · subst j; simpa [g] using hz
    · simpa [g,eq] using pos j
  have sum : (∑j,g j)=Fintype.card J+1 := by simp [g,Finset.sum_add_distrib]
  have eq (j:J) : f j=g j := by
    by_contra diff
    have lt := Finset.sum_lt_sum (s:=Finset.univ) (fun i _ => le i)
      ⟨j,Finset.mem_univ j,lt_of_le_of_ne (le j) (Ne.symm diff)⟩
    omega
  exact ⟨z,by simpa [g] using eq z,fun j ne => by simpa [g,ne] using eq j⟩

omit [Finite X] in
private theorem no_triple_original_image (Q : SimpleGraph X) (I : Set X) (B : Set ↥(Iᶜ : Set X))
    (small : NoIndependentTriple ((Q.induce Iᶜ).induce B)) :
    NoIndependentTriple (Q.induce (Subtype.val '' B)) := by
  rintro ⟨_,a,ha,rfl⟩ ⟨_,b,hb,rfl⟩ ⟨_,c,hc,rfl⟩ ab ac bc
  exact small ⟨a,ha⟩ ⟨b,hb⟩ ⟨c,hc⟩
    (fun eq => ab (Subtype.ext (congrArg (fun w:B => w.val.val) eq)))
    (fun eq => ac (Subtype.ext (congrArg (fun w:B => w.val.val) eq)))
    (fun eq => bc (Subtype.ext (congrArg (fun w:B => w.val.val) eq)))

/-- The larger odd part has one exceptional root degree of two. All its
other vertices have one root neighbour and can each be exposed internally. -/
theorem detached_pair_profile_at_large_size (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (s : DetachedMatePair (Q.induce Iᶜ))
    (size : (Subtype.val '' s.preferred).ncard=D+1)
    (cost : crossCount Q (Subtype.val '' s.preferred) (Subtype.val '' s.preferred)ᶜ=D+2)
    (small : NoIndependentTriple ((Q.induce Iᶜ).induce s.preferred)) :
    let B := Subtype.val '' s.preferred
    PerfectAfterEveryDeletion (Q.induce B) ∧
      ∃z:B,(Q.neighborSet z.val∩I).ncard=2 ∧ ∀v:B,v≠z → (Q.neighborSet v.val∩I).ncard=1 := by
  intro B
  classical
  let _ := Fintype.ofFinite B
  change B.ncard=D+1 at size
  change crossCount Q B Bᶜ=D+2 at cost
  have outside : B⊆Iᶜ := by rintro _ ⟨v,_,rfl⟩;exact v.property
  have away : Disjoint I B := Set.disjoint_left.mpr (fun _ hi hb => outside hb hi)
  have ext (v:B) : Q.neighborSet v.val∩Bᶜ=Q.neighborSet v.val∩I := by
    ext u
    constructor
    · rintro ⟨edge,out⟩
      refine ⟨edge,?_⟩
      by_contra far
      let t : ↥(Iᶜ : Set X) := ⟨u,far⟩
      obtain ⟨w,hw,e⟩ := v.property
      have adj : (Q.induce Iᶜ).Adj w t := (show Q.Adj w.val u from e.symm ▸ edge)
      rcases s.cover t with hs|hc|hp
      · exact s.isolated t hs w adj.symm
      · exact s.apart_edges w hw t hc adj
      · exact out ⟨t,hp,rfl⟩
    · rintro ⟨edge,ui⟩;exact ⟨edge,fun hb => outside hb ui⟩
  let f (v:B) := (Q.neighborSet v.val∩I).ncard
  have positive (v:B) : 1≤f v := by
    obtain ⟨u,ui,adj⟩ := largest_independent_dominates Q I ind largest v.val (outside v.property)
    exact (Set.ncard_pos (Set.toFinite _)).mpr ⟨u,adj,ui⟩
  have sum : ∑v,f v=Fintype.card B+1 := by
    rw [crossCount_eq_neighbor_sum] at cost
    simp_rw [ext] at cost
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,size]
    exact cost.trans (by omega)
  have odd : Odd (Nat.card B) := by rw [Nat.card_coe_set_eq,size];exact Even.add_one par
  refine ⟨critical_of_odd_small_alpha _ odd (no_triple_original_image Q I _ small) ?_,one_excess_label f positive sum⟩
  intro u
  by_contra cut
  have high := cut_vertex_boundary_outside_largest_independent Q I B D reg ind largest away u cut
  omega

#print axioms detached_pair_profile_at_large_size
end JSP452Audit.StarHost
