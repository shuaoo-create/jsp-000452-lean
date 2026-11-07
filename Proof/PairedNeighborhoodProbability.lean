import PairedTenStateMasks
namespace JSP452Audit.StarHost

/-- Which of the two labels of coordinate i occur in a given neighbourhood. -/
noncomputable def pairSidesAt {V I : Type*} (key : V ↪ I×Bool) (N : Set V) (i:I) : Finset Bool := by
  classical
  exact Finset.univ.filter (fun b => ∃v∈N,key v=(i,b))

theorem mem_pair_sides {V I : Type*} (key : V ↪ I×Bool) (N : Set V) (i:I) (b:Bool) :
    b∈pairSidesAt key N i ↔ ∃v∈N,key v=(i,b) := by
  classical
  simp [pairSidesAt]

theorem pair_side_count_sum {V I : Type*} [Finite V] [Fintype I] (key : V ↪ I×Bool) (N : Set V) :
    (∑i:I,(pairSidesAt key N i).card)=N.ncard := by
  classical
  let P := Σi:I,↥(pairSidesAt key N i)
  let pack (u:P) : I×Bool := (u.1,u.2.val)
  have uniq : Function.Injective pack := by
    rintro ⟨i,b⟩ ⟨j,c⟩ eq
    have h : i=j := congrArg Prod.fst eq
    subst j
    have same : b=c := Subtype.ext (congrArg Prod.snd eq)
    cases same;rfl
  let send (v:N) : P := ⟨(key v.val).1,⟨(key v.val).2,(mem_pair_sides _ _ _ _).2 ⟨v.val,v.property,rfl⟩⟩⟩
  have inj : Function.Injective send := fun a b eq => Subtype.ext (key.injective (congrArg pack eq))
  have onto : Function.Surjective send := by
    rintro ⟨i,b⟩
    obtain ⟨v,hv,hit⟩ := (mem_pair_sides _ _ _ _).1 b.property
    exact ⟨⟨v,hv⟩,uniq hit⟩
  have eq := Nat.card_congr (Equiv.ofBijective send ⟨inj,onto⟩)
  change Nat.card N=Nat.card (Σi:I,↥(pairSidesAt key N i)) at eq
  rw [Nat.card_sigma,Nat.card_coe_set_eq] at eq
  simp only [Nat.card_eq_fintype_card,Fintype.card_coe] at eq
  exact eq.symm

/-- The exact joint miss count factors over coordinates, including when
two distinct adjacent vertices share the same coordinate. -/
theorem paired_miss_weight {V I : Type*} [Finite V] [Fintype I] (key : V ↪ I×Bool) (N : Set V) :
    (Nat.card {f:I→Fin 10 // ∀v∈N,¬pairMaskSelect (key v).2 (f (key v).1)}:ℚ)=
      (10:ℚ)^(Nat.card I)*∏i:I,((pairAllowed (pairSidesAt key N i)).card:ℚ)/10 := by
  classical
  let L := I→Fin 10
  let tags := pairSidesAt key N
  let C (i:I) := pairAllowed (tags i)
  have eq : {f:L | ∀v∈N,¬pairMaskSelect (key v).2 (f (key v).1)}=
      {f:L | ∀i,f i∈C i} := by
    ext f
    constructor
    · intro miss i
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      intro b hb
      obtain ⟨v,hv,keyEq⟩ := (mem_pair_sides _ _ _ _).1 hb
      have no := miss v hv
      rw [keyEq] at no;exact no
    · intro eligible v hv
      have rest := (Finset.mem_filter.mp (eligible (key v).1)).2
      exact rest _ ((mem_pair_sides _ _ _ _).2 ⟨v,hv,rfl⟩)
  change (Nat.card ↥({f:L | ∀v∈N,¬pairMaskSelect (key v).2 (f (key v).1)}:Set L):ℚ)=_
  rw [eq];exact paired_coordinate_weight C

/-- A full coordinate inside the neighbourhood realizes the extra factor
40/49 beyond independent one-label sampling. -/
theorem paired_miss_bounds {V I : Type*} [Finite V] [Fintype I] (key : V ↪ I×Bool) (N : Set V) :
    let cost := (Nat.card {f:I→Fin 10 // ∀v∈N,¬pairMaskSelect (key v).2 (f (key v).1)}:ℚ)
    let den := (10:ℚ)^(Nat.card I)
    cost≤den*(7/10:ℚ)^N.ncard ∧
      ∀i:I,(pairSidesAt key N i).card=2 → cost≤den*((40/49:ℚ)*(7/10:ℚ)^N.ncard) := by
  intro cost den
  classical
  let S := pairSidesAt key N
  let w (i:I) := ((pairAllowed (S i)).card:ℚ)/10
  let q : ℚ := 7/10
  have pw : (∏i:I,q^(S i).card)=q^N.ncard := by
    rw [Finset.prod_pow_eq_pow_sum,pair_side_count_sum]
  have count : cost=den*∏i:I,w i := paired_miss_weight key N
  have positive : 0≤den := by dsimp [den];positivity
  have w0 (i:I) : 0≤w i := div_nonneg (Nat.cast_nonneg _) (by norm_num)
  rw [count]
  constructor
  · apply mul_le_mul_of_nonneg_left _ positive
    change _≤q^N.ncard
    rw [←pw]
    exact Finset.prod_le_prod (fun i _ => w0 i) (fun i _ => pair_allowed_rate (S i))
  · intro k two
    apply mul_le_mul_of_nonneg_left _ positive
    let delta (i:I) : ℚ := if i=k then 40/49 else 1
    have each (i:I) : w i≤delta i*q^(S i).card := by
      by_cases eq:i=k
      · subst i
        simpa [w,delta,q] using (pair_allowed_discount (S k) two).le
      · simpa [delta,eq,q] using pair_allowed_rate (S i)
    have cmp := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => w0 i)
      (fun i _ => each i)
    rw [Finset.prod_mul_distrib,pw] at cmp
    have onlyK : (∏i:I,delta i)=40/49 := by simp [delta,Finset.prod_ite_eq']
    rwa [onlyK] at cmp

#print axioms pair_side_count_sum
#print axioms paired_miss_weight
#print axioms paired_miss_bounds
end JSP452Audit.StarHost
