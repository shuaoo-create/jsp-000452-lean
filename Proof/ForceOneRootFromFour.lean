import BadSingleCutFromFour
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

omit [Nonempty X] in
private theorem root_plus_internal_cap (Q : SimpleGraph X) (I T : Set X) (v : X)
    (D : ℕ) (reg : Nat.card (Q.neighborSet v)=D)
    (outside : T⊆Iᶜ) (neighbors : T⊆Q.neighborSet v) :
    (Q.neighborSet v∩I).ncard+T.ncard≤D := by
  have dis : Disjoint (Q.neighborSet v∩I) T := Set.disjoint_left.mpr (fun _ a b => outside b a.2)
  have sub : (Q.neighborSet v∩I)∪T ⊆ Q.neighborSet v := Set.union_subset Set.inter_subset_left neighbors
  rw [←Set.ncard_union_eq dis]
  exact (Set.ncard_le_ncard sub).trans ((Nat.card_coe_set_eq _).symm.trans reg).le

/-- In the remaining one-cut shape, choose a root missing the cut and one
clique vertex, together with the forced exit root and its single-owner witness. -/
theorem forced_root_and_missing_pair_from_four (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (many : 3≤I.ncard) (D : ℕ) (four : 4≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q D=0)
    (s : OnePreferredPart Q I) (conn : (Q.induce s.preferred).Preconnected)
    (small : NoIndependentTriple (Q.induce s.preferred)) (x : s.preferred)
    (bad : ¬ ExposablePoint (Q.induce s.preferred) x) (shape : BadSingleSplit Q s.preferred x.val D) :
    ∃ r∈I,∃i∈I, i≠r ∧ ∃a∈shape.side, ∃w∈shape.side,
      ¬Q.Adj x.val a ∧ ¬Q.Adj i a ∧ ¬Q.Adj i x.val ∧ Q.Adj r shape.leaf ∧
      Q.Adj r w ∧ (∀j∈I,Q.Adj j w → j=r) := by
  classical
  let P := s.preferred
  let A := shape.side
  let b := shape.leaf
  have sub : A⊆P\{x.val} := shape.parts ▸ Set.subset_union_left
  have bp : b∈P := (shape.parts ▸ (show b∈A∪{b} from Or.inr (by simp)) : b∈P\{x.val}).1
  have outside : A⊆Iᶜ := fun v hv => s.pOut (sub hv).1
  have oddP : Odd (Nat.card P) := by rw [Nat.card_coe_set_eq];exact s.odd
  have exposed (v:P) (ne:v≠x) : ExposablePoint (Q.induce P) v :=
    every_other_vertex_exposable _ conn oddP small x bad v ne
  have inner (z:X) (hz:z∈A) : A\{z} ⊆ Q.neighborSet z := by
    intro v h;exact shape.clique hz h.1 (fun eq => h.2 (Set.mem_singleton_iff.mpr eq.symm))
  have sideSize : A.ncard=D-1 := shape.order
  have capA (z:X) (hz:z∈A) : (Q.neighborSet z∩I).ncard≤2 := by
    have h := root_plus_internal_cap Q I (A\{z}) z D (reg _) (fun v hv => outside hv.1) (inner z hz)
    have count := Set.ncard_sdiff_singleton_add_one hz
    omega
  obtain ⟨w,hw,xw⟩ := shape.near
  change w∈A at hw
  have bf : b∉A := shape.distinct
  have capW : (Q.neighborSet w∩I).ncard≤1 := by
    let T := insert x.val (A\{w})
    have nb : T⊆Q.neighborSet w := by rintro v (eq|mem); exact eq.symm ▸ xw.symm;exact inner w hw mem
    have out : T⊆Iᶜ := by rintro v (eq|mem);exact eq.symm ▸ s.pOut x.property;exact outside mem.1
    have h := root_plus_internal_cap Q I T w D (reg _) out nb
    have xx : x.val∉A\{w} := fun h => shape.off h.1
    have n : T.ncard=(A\{w}).ncard+1 := Set.ncard_insert_of_notMem xx
    have loss := Set.ncard_sdiff_singleton_add_one hw
    omega
  obtain ⟨r,ri,wr⟩ := largest_independent_dominates Q I ind largest w (outside hw)
  have unique (j:X) (ji:j∈I) (edge:Q.Adj j w) : j=r :=
    (Set.ncard_le_one (Set.toFinite _)).mp capW j ⟨edge.symm,ji⟩ r ⟨wr,ri⟩
  have wx : w≠x.val := fun eq => shape.off (eq ▸ hw)
  have other {v:X} (vp:v∈P) (vx:v≠x.val) (miss : ¬Q.Adj r v) (i:X) (hi:i∈I) (ir:i≠r) : Q.Adj i v := by
    obtain ⟨u,hu,_,pair⟩ := single_part_exposable_cover Q I ind D (by omega) reg crit zero s i hi
    have up : u=r := by
      rcases pair ⟨w,(sub hw).1⟩ (exposed _ (fun eq => wx (congrArg Subtype.val eq))) with h|h
      · exact (ir (unique i hi h)).elim
      · exact unique u hu h
    rcases pair ⟨v,vp⟩ (exposed _ (fun eq => vx (congrArg Subtype.val eq))) with h|h
    · exact h
    · exact (miss (up ▸ h)).elim
  have deficient {v:X} (vp:v∈P) (vx:v≠x.val) (miss : ¬Q.Adj r v) :
      I.ncard≤(Q.neighborSet v∩I).ncard+1 := by
    have inc : I\{r}⊆Q.neighborSet v∩I := fun i h =>
      ⟨(other vp vx miss i h.1 (by simpa using h.2)).symm,h.1⟩
    have bound := Set.ncard_le_ncard inc
    have card := Set.ncard_sdiff_singleton_add_one ri
    omega
  have rootCount := single_part_root_degree Q I D reg s many
  have toward (a:X) (ha:a∈A) : Q.Adj r a := by
    by_contra miss
    have d := deficient (sub ha).1 (by simpa using (sub ha).2) miss
    have h := capA a ha
    omega
  have extra : D<I.ncard := by
    by_contra! tooFew
    have all (v:X) (hv:v∈s.singles) : Q.Adj r v := by
      have eq : Q.neighborSet v=I := Set.eq_of_subset_of_ncard_le (s.isolated v hv)
        (by rw [←Nat.card_coe_set_eq (Q.neighborSet v),reg];omega)
      have mem : r∈Q.neighborSet v := by rw [eq];exact ri
      exact (show Q.Adj v r from mem).symm
    have manyNb : s.singles∪A⊆Q.neighborSet r := fun v h => h.elim (all v) (toward v)
    have n := Set.ncard_le_ncard manyNb
    rw [Set.ncard_union_eq (s.dis.mono_right (fun v hv => (sub hv).1)),
      ←Nat.card_coe_set_eq (Q.neighborSet r),reg] at n
    have c:=s.count
    omega
  have rb : Q.Adj r b := by
    by_contra miss
    have too := deficient bp shape.leaf_off miss
    have n := root_plus_internal_cap Q I {x.val} b D (reg _) (fun _ e =>
      (Set.mem_singleton_iff.mp e).symm ▸ s.pOut x.property) (fun _ e =>
      (Set.mem_singleton_iff.mp e).symm ▸ shape.to_leaf.symm)
    rw [Set.ncard_singleton] at n;omega
  obtain ⟨u,ui,xu⟩ := largest_independent_dominates Q I ind largest x.val (s.pOut x.property)
  have missing : ∃a∈A,¬Q.Adj x.val a := by
    by_contra! all
    have subset : insert b A⊆Q.neighborSet x.val := by
      rintro v (eq|ha);exact eq.symm ▸ shape.to_leaf;exact all v ha
    have nb := root_plus_internal_cap Q I (insert b A) x.val D (reg _)
      (by rintro v (e|h);exact e.symm ▸ s.pOut bp;exact outside h) subset
    have positive := (Set.ncard_pos (Set.toFinite (Q.neighborSet x.val∩I))).mpr ⟨u,xu,ui⟩
    rw [Set.ncard_insert_of_notMem bf] at nb;omega
  obtain ⟨a,ha,xa⟩ := missing
  have capX : (Q.neighborSet x.val∩I).ncard≤D-2 := by
    have wb : w≠b := fun eq => bf (eq ▸ hw)
    have n := root_plus_internal_cap Q I ({w,b} : Set X) x.val D (reg _)
      (by rintro v (e|e);exact e.symm ▸ outside hw;exact (Set.mem_singleton_iff.mp e).symm ▸ s.pOut bp)
      (by rintro v (e|e);exact e.symm ▸ xw;exact (Set.mem_singleton_iff.mp e).symm ▸ shape.to_leaf)
    rw [Set.ncard_pair wb] at n;omega
  let F := (Q.neighborSet x.val∩I)∪(Q.neighborSet a∩I)
  have fcap := Set.ncard_union_le (Q.neighborSet x.val∩I) (Q.neighborSet a∩I)
  have cap := capA a ha
  obtain ⟨i,hi,avoid⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
    (show F.ncard<I.ncard from (by change F.ncard≤_ at fcap;omega))
  have ia : ¬Q.Adj i a := fun h => avoid (Or.inr ⟨h.symm,hi⟩)
  have ix : ¬Q.Adj i x.val := fun h => avoid (Or.inl ⟨h.symm,hi⟩)
  exact ⟨r,ri,i,hi,fun eq => ia (eq.symm ▸ toward a ha),a,ha,w,hw,xa,ia,ix,rb,wr.symm,unique⟩

#print axioms forced_root_and_missing_pair_from_four
end JSP452Audit.StarHost
