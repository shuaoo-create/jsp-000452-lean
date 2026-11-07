import ExceptionalRankBudget
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private def threeLabels (a b c : X) (i : Fin 3) : X :=
  if i=0 then a else if i=1 then b else c

private def threeEmbedding {a b c : X} (ab : a≠b) (ac : a≠c) (bc : b≠c) : Fin 3 ↪ X where
  toFun := threeLabels a b c
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [threeLabels,Ne.symm ab,Ne.symm ac,Ne.symm bc]

private theorem rank_after_cut {J : Type*} [Finite J] (Q : SimpleGraph X) (Y C : Set X)
    (inside : C⊆Yᶜ) (cl : Q.IsClique C) (even : Even C.ncard) (l r : J ↪ X)
    (lkeep : ∀j,l j∉Y) (rkeep : ∀j,r j∉Y) (edge : ∀j,Q.Adj (l j) (r j))
    (apart : Disjoint (Set.range l) (Set.range r))
    (free : Disjoint C (Set.range l∪Set.range r)) :
    C.ncard+2*Nat.card J≤2*matchingEdges (Q.induce Yᶜ) := by
  let T : Set ↥(Yᶜ : Set X) := {v | v.val∈C}
  let v : J ↪ ↥(Yᶜ : Set X) := ⟨fun j => ⟨l j,lkeep j⟩,fun _ _ eq => l.injective (congrArg Subtype.val eq)⟩
  let w : J ↪ ↥(Yᶜ : Set X) := ⟨fun j => ⟨r j,rkeep j⟩,fun _ _ eq => r.injective (congrArg Subtype.val eq)⟩
  have image : Subtype.val '' T=C := by
    ext t;exact ⟨fun ⟨z,h,e⟩ => e ▸ h,fun h => ⟨⟨t,inside h⟩,h,rfl⟩⟩
  have size := (Set.ncard_image_of_injective T Subtype.val_injective).symm.trans (congrArg Set.ncard image)
  have d : Disjoint (Set.range v) (Set.range w) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨j,rfl⟩ ⟨k,eq⟩
    have same : r k=l j := congrArg Subtype.val eq
    exact Set.disjoint_left.mp apart (Set.mem_range_self j) (same ▸ Set.mem_range_self k)
  have out : Disjoint T (Set.range v∪Set.range w) := by
    apply Set.disjoint_left.mpr
    rintro z cz (⟨j,rfl⟩|⟨k,rfl⟩)
    · exact Set.disjoint_left.mp free cz (Or.inl (Set.mem_range_self j))
    · exact Set.disjoint_left.mp free cz (Or.inr (Set.mem_range_self k))
  have bound := even_clique_and_edge_family_rank (Q.induce Yᶜ) T
    (fun {a} ha {b} hb ne => cl ha hb (fun eq => ne (Subtype.ext eq))) (size.symm ▸ even)
    v w (fun j => edge j) d out
  rwa [size] at bound

/-- Two disjoint edges from the big clique into roots different from a
chosen neighbour of the pivot contradict Liu's zero-reserve rank equality. -/
theorem no_two_clique_root_edges [Nonempty X] (Q : SimpleGraph X) (I : Set X)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q D=0)
    (s : HeavyCliqueFrame Q I D) (r : X) (ri:r∈I) (ar : Q.Adj s.pivot r)
    (c e i j : X) (cc:c∈s.cliquePart) (ec:e∈s.cliquePart) (ce:c≠e)
    (ii:i∈I) (ji:j∈I) (ir:i≠r) (jr:j≠r) (ij:i≠j)
    (ic : Q.Adj c i) (je : Q.Adj e j) : False := by
  classical
  let C := s.cliquePart
  obtain ⟨z,zc,avoid⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show ({c,e} : Set X).ncard<C.ncard from (by rw [Set.ncard_pair ce,show C.ncard=D-1 from s.order];omega))
  have zc' : z≠c := fun eq => avoid (Or.inl eq)
  have ze : z≠e := fun eq => avoid (Or.inr (Set.mem_singleton_iff.mpr eq))
  let Y := insert z s.singles
  let B := C\{z,c,e}
  let l : Fin 3 ↪ X := threeEmbedding (show s.pivot≠c from fun eq => s.ac (eq.symm ▸ cc))
    (show s.pivot≠e from fun eq => s.ac (eq.symm ▸ ec)) ce
  let t : Fin 3 ↪ X := threeEmbedding ir.symm jr.symm ij
  have lval (v : Fin 3) : l v=s.pivot ∨ l v=c ∨ l v=e := by
    fin_cases v <;> first | exact Or.inl rfl | exact Or.inr (Or.inl rfl) | exact Or.inr (Or.inr rfl)
  have ti (v:Fin 3) : t v∈I := by fin_cases v <;> first | exact ri | exact ii | exact ji
  have lout (v:Fin 3) : l v∉I := by
    rcases lval v with h|h|h
    · exact h.symm ▸ s.ai
    · exact h.symm ▸ s.cOut cc
    · exact h.symm ▸ s.cOut ec
  have lkeep (v:Fin 3) : l v∉Y := by
    rcases lval v with hp|hc|he <;> rintro (vz|vs)
    · exact s.ac ((vz.symm.trans hp) ▸ zc)
    · exact s.as_ (hp ▸ vs)
    · exact zc' (vz.symm.trans hc)
    · exact Set.disjoint_left.mp s.dis (hc ▸ vs) cc
    · exact ze (vz.symm.trans he)
    · exact Set.disjoint_left.mp s.dis (he ▸ vs) ec
  have rkeep (v:Fin 3) : t v∉Y := by
    rintro (hz|hs)
    · exact s.cOut zc (hz ▸ ti v)
    · exact s.sOut hs (ti v)
  have bkeep : B⊆Yᶜ := by
    intro v hv
    rintro (eq|hs)
    · exact hv.2 (Or.inl eq)
    · exact Set.disjoint_left.mp s.dis hs hv.1
  have inc : ({z,c,e} : Set X)⊆C := by
    rintro v (h|h|h)
    · exact h.symm ▸ zc
    · exact h.symm ▸ cc
    · exact (Set.mem_singleton_iff.mp h).symm ▸ ec
  have removed := Set.ncard_sdiff_add_ncard_of_subset inc
  rw [Set.ncard_insert_of_notMem (by simpa using avoid),Set.ncard_pair ce] at removed
  change B.ncard+(2+1)=C.ncard at removed
  have csize : C.ncard=D-1 := s.order
  have evenB : Even B.ncard := by have ep := Nat.even_iff.mp par;rw [Nat.even_iff];omega
  have edges (v:Fin 3) : Q.Adj (l v) (t v) := by fin_cases v <;> first | exact ar | exact ic | exact je
  have dis : Disjoint (Set.range l) (Set.range t) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨v,rfl⟩ ⟨w,eq⟩
    exact lout v (eq ▸ ti w)
  have free : Disjoint B (Set.range l∪Set.range t) := by
    apply Set.disjoint_left.mpr
    rintro v hv (⟨u,rfl⟩|⟨w,rfl⟩)
    · rcases lval u with h|h|h
      · exact s.ac (h ▸ hv.1)
      · exact hv.2 (Or.inr (Or.inl h))
      · exact hv.2 (Or.inr (Or.inr (Set.mem_singleton_iff.mpr h)))
    · exact s.cOut hv.1 (ti w)
  have bound := rank_after_cut Q Y B bkeep (s.clique.subset (fun _ h => h.1)) evenB
    l t lkeep rkeep edges dis free
  have equality := independent_cut_leaves_half_rank Q I D four reg crit zero s z zc
  change 2*matchingEdges (Q.induce Yᶜ)=D at equality
  rw [Nat.card_fin,equality] at bound
  omega

#print axioms no_two_clique_root_edges
end JSP452Audit.StarHost
