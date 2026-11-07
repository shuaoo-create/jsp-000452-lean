import PairedNeighborhoodProbability
namespace JSP452Audit.StarHost

private theorem nat_indicator {A : Type*} [Fintype A] (cond : A→Prop) [DecidablePred cond] :
    (∑a:A,if cond a then (1:ℕ) else 0)=Nat.card {a // cond a} := by
  rw [Finset.sum_boole,Nat.card_eq_fintype_card,Fintype.card_subtype]
  rfl

private theorem sum_incidence_counts {L T : Type*} [Fintype L] [Fintype T] (P : L→T→Prop) :
    (∑l:L,({t | P l t}:Set T).ncard) = ∑t:T,Nat.card {l // P l t} := by
  classical
  calc
    _ = ∑l:L,∑t:T,if P l t then 1 else 0 := by
      apply Finset.sum_congr rfl;intro l _
      rw [nat_indicator,←Nat.card_coe_set_eq]
      rfl
    _ = ∑t:T,∑l:L,if P l t then 1 else 0 := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl (fun t _ => nat_indicator _)

theorem paired_selected_weight {I : Type*} [Fintype I] (i:I) (b:Bool) :
    (Nat.card {f:I→Fin 10 // pairMaskSelect b (f i)}:ℚ)=(10:ℚ)^(Nat.card I)*(3/10) := by
  classical
  let H : Finset (Fin 10) := Finset.univ.filter (pairMaskSelect b)
  have hc : H.card=3 := by
    change (Finset.univ.filter (pairMaskSelect b)).card=3
    cases b <;> decide
  let C (j:I) : Finset (Fin 10) := if j=i then H else Finset.univ
  have eq : {f:I→Fin 10 | pairMaskSelect b (f i)}={f | ∀j,f j∈C j} := by
    ext f
    constructor
    · intro present j
      by_cases h:j=i
      · subst j
        simpa [C,H] using present
      · simp [C,h]
    · intro allowed
      have h := allowed i
      simpa [C,H] using h
  have ratio (j:I) : ((C j).card:ℚ)/10=(if j=i then 3/10 else 1:ℚ) := by
    by_cases eq:j=i <;> simp [C,eq,hc] <;> norm_num
  change (Nat.card ↥({f:I→Fin 10 | pairMaskSelect b (f i)}:Set (I→Fin 10)):ℚ)=_
  rw [eq]
  change (Nat.card {f:I→Fin 10 // ∀j,f j∈C j}:ℚ)=_
  rw [paired_coordinate_weight C]
  simp_rw [ratio]
  simp [Finset.prod_ite_eq']

/-- A single finite paired sample, with repaired misses, hits all the
neighbourhoods. A prescribed subclass gets the two-label discount. -/
theorem paired_sample_transversal {V I T : Type*} [Fintype V] [Fintype I] [Fintype T]
    (key : V ↪ I×Bool) (N : T→Set V) (nonempty : ∀t,(N t).Nonempty) (marked : Set T) [DecidablePred (·∈marked)]
    (together : ∀t∈marked,∃i,(pairSidesAt key (N t) i).card=2) :
    ∃S:Set V,(∀t,∃v∈S,v∈N t) ∧ (S.ncard:ℚ)≤(3/10)*(Nat.card V:ℚ)+
      ∑t:T,(if t∈marked then (40/49:ℚ) else 1)*(7/10:ℚ)^(N t).ncard := by
  classical
  let L := I→Fin 10
  let chosen (f:L) (v:V) := pairMaskSelect (key v).2 (f (key v).1)
  let pick (f:L) := {v:V | chosen f v}
  let miss (f:L) := {t:T | ∀v∈N t,¬chosen f v}
  let den : ℚ := 10^(Nat.card I)
  let rate (t:T) := (if t∈marked then (40/49:ℚ) else 1)*(7/10:ℚ)^(N t).ncard
  let bound : ℚ := (3/10)*(Nat.card V:ℚ)+∑t:T,rate t
  have vNat := sum_incidence_counts chosen
  have tNat := sum_incidence_counts (fun (f:L) (t:T) => ∀v∈N t,¬chosen f v)
  have pickSum : (∑f:L,((pick f).ncard:ℚ))=den*((3/10)*(Nat.card V:ℚ)) := by
    have cast : (∑f:L,((pick f).ncard:ℚ))=∑v:V,(Nat.card {f:L // chosen f v}:ℚ) := by exact_mod_cast vNat
    rw [cast,Finset.sum_congr rfl (fun (v:V) (_ : v∈Finset.univ) => paired_selected_weight (key v).1 (key v).2)]
    rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul];dsimp [den];ring
  have each (t:T) : (Nat.card {f:L // ∀v∈N t,¬chosen f v}:ℚ)≤den*rate t := by
    have weight := paired_miss_bounds key (N t)
    by_cases yes:t∈marked
    · obtain ⟨i,tag⟩ := together t yes
      simpa only [rate,if_pos yes] using weight.2 i tag
    · simpa only [rate,if_neg yes,one_mul] using weight.1
  have missSum : (∑f:L,((miss f).ncard:ℚ))≤den*(∑t:T,rate t) := by
    have cast : (∑f:L,((miss f).ncard:ℚ))=∑t:T,(Nat.card {f:L // ∀v∈N t,¬chosen f v}:ℚ) := by exact_mod_cast tNat
    rw [cast,Finset.mul_sum];exact Finset.sum_le_sum (fun t _ => each t)
  have card : (Fintype.card L:ℚ)=den := by
    rw [←Nat.card_eq_fintype_card];change (Nat.card (I→Fin 10):ℚ)=_
    rw [Nat.card_fun,Nat.card_fin];push_cast;rfl
  have good : ∃f:L,((pick f).ncard:ℚ)+(miss f).ncard≤bound := by
    by_contra! none
    let zero : L := fun _ => 0
    have lt := Finset.sum_lt_sum (s:=(Finset.univ : Finset L)) (fun f _ => (none f).le)
      ⟨zero,Finset.mem_univ _,none zero⟩
    have total : (∑f:L,(((pick f).ncard:ℚ)+(miss f).ncard))≤den*bound := by
      rw [Finset.sum_add_distrib,pickSum];dsimp only [bound];rw [mul_add];linarith
    have constant : (∑_f:L,bound)=den*bound := by rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,card]
    rw [constant] at lt;exact (not_lt_of_ge total) lt
  obtain ⟨f,small⟩ := good
  choose rescue legal using nonempty
  let S := pick f∪(rescue '' miss f)
  have size := (Set.ncard_union_le (pick f) (rescue '' miss f)).trans
    (Nat.add_le_add_left (Set.ncard_image_le (f:=rescue) (s:=miss f)) _)
  have real : (S.ncard:ℚ)≤((pick f).ncard:ℚ)+(miss f).ncard := by exact_mod_cast size
  refine ⟨S,?_,real.trans small⟩
  intro t
  by_cases hits : ∃v∈N t,chosen f v
  · obtain ⟨v,hv,hit⟩ := hits;exact ⟨v,Or.inl hit,hv⟩
  have mt : t∈miss f := fun v hv hit => hits ⟨v,hv,hit⟩
  exact ⟨rescue t,Or.inr ⟨t,mt,rfl⟩,legal t⟩

#print axioms paired_selected_weight
#print axioms paired_sample_transversal
end JSP452Audit.StarHost
