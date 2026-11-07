import SingleBadCutShape
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem clique_min_cost (D n : ℕ) (lo : 2≤n) (hi : n≤D-1) : 2*D-2≤n*(D+1-n) := by
  let a:=n-2
  let b:=D-1-n
  have size : n=a+2 := by dsimp [a];omega
  have gap : D+1-n=b+2 := by dsimp [b];omega
  have degree : D=a+b+3 := by dsimp [a,b];omega
  rw [gap,size,Nat.add_mul,Nat.mul_add];omega

/-- A nonexposable vertex splits a large connected preferred part into a
D−1 clique and a singleton, on the original labels. -/
theorem split_large_bad_single_from_four (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (s : OnePreferredPart Q I) (large : D+1≤s.preferred.ncard)
    (conn : (Q.induce s.preferred).Preconnected) (small : NoIndependentTriple (Q.induce s.preferred))
    (x : s.preferred) (bad : ¬ExposablePoint (Q.induce s.preferred) x) :
    Nonempty (BadSingleSplit Q s.preferred x.val D) := by
  classical
  let P := s.preferred
  let S := s.singles
  have cut : ¬((Q.induce P).induce {v | v≠x}).Preconnected := by
    intro c
    apply bad
    apply perfect_of_preconnected_even_no_independent_triple _ c _ (small.induce _)
    have h : {v : P | v≠x}=({x} : Set P)ᶜ := by ext;simp
    rw [Nat.card_coe_set_eq,h,Set.ncard_compl,Set.ncard_singleton,Nat.card_coe_set_eq,Nat.even_iff]
    have par := Nat.odd_iff.mp s.odd
    omega
  obtain ⟨L,R,ln,rn,lr,parts,cl,cr,sep,nearL,nearR⟩ := labelled_cut_sides Q P x conn small cut
  have lsub : L⊆P\{x.val} := parts ▸ Set.subset_union_left
  have rsub : R⊆P\{x.val} := parts ▸ Set.subset_union_right
  have xp := x.property
  have xi := s.pOut xp
  let K := insert x.val I
  let C : Fin 3→Set X := fun i => if i=0 then S else if i=1 then L else R
  have sl : Disjoint S L := s.dis.mono_right (fun v hv => (lsub hv).1)
  have sr : Disjoint S R := s.dis.mono_right (fun v hv => (rsub hv).1)
  have outsideL : L⊆Kᶜ := by
    rintro v hv (e|h)
    · exact (lsub hv).2 (Set.mem_singleton_iff.mpr e)
    · exact s.pOut (lsub hv).1 h
  have outsideR : R⊆Kᶜ := by
    rintro v hv (e|h)
    · exact (rsub hv).2 (Set.mem_singleton_iff.mpr e)
    · exact s.pOut (rsub hv).1 h
  have outS : S⊆Kᶜ := by
    rintro v hv (e|h)
    · exact Set.disjoint_left.mp s.dis hv (e.symm ▸ xp)
    · exact s.sOut hv h
  have dis (i j : Fin 3) (ne:i≠j) : Disjoint (C i) (C j) := by
    fin_cases i <;> fin_cases j <;> simp_all [C,lr,lr.symm,sl,sl.symm,sr,sr.symm]
  have outs (i:Fin 3) : C i⊆Kᶜ := by fin_cases i <;> first | exact outS | exact outsideL | exact outsideR
  have extSide (A B : Set X) (sub : A⊆P\{x.val}) (cover : A∪B=P\{x.val})
      (separate : ∀a∈A,∀b∈B,¬Q.Adj a b)
      (a:X) (ha:a∈A) (v:X) (edge:Q.Adj a v) (away:v∉A) : v∈K := by
    by_cases eq : v=x.val
    · exact Or.inl eq
    by_cases mem : v∈P
    · have either : v∈A∪B := cover.symm ▸ (show v∈P\{x.val} from ⟨mem,by simpa using eq⟩)
      exact (separate a ha v (either.resolve_left away) edge).elim
    · exact Or.inr (s.external a (sub ha).1 v edge mem)
  have external (j:Fin 3) (a:X) (ha:a∈C j) (v:X) (edge:Q.Adj a v) (away:v∉C j) : v∈K := by
    fin_cases j
    · exact Or.inr (s.isolated a ha v edge)
    · exact extSide L R lsub parts sep a ha v edge away
    · exact extSide R L rsub (by rw [Set.union_comm,parts]) (fun b hb a ha e => sep a ha b hb e.symm) a ha v edge away
  obtain ⟨i,hi,adj⟩ := largest_independent_dominates Q I ind largest x.val xi
  have internal : ∃a∈K,∃b∈K,Q.Adj a b := ⟨x.val,Or.inl rfl,i,Or.inr hi,adj⟩
  have total := split_roots_cut_cap Q C K D dis outs external reg internal
  have kc : K.ncard=S.ncard+3 := by
    rw [show K=insert x.val I from rfl,Set.ncard_insert_of_notMem xi,←s.count]
  have scost : crossCount Q S Sᶜ=S.ncard*D := by
    rw [crossCount_swap]
    exact uniform_cross_count Q S Sᶜ D (by
      intro v hv
      have sub : Q.neighborSet v ⊆ Sᶜ := fun w adj hw => s.sOut hw (s.isolated v hv w adj)
      rw [Set.inter_eq_left.mpr sub,←Nat.card_coe_set_eq,reg])
  have sum (f:Fin 3→ℕ) : (∑i,f i)=f 0+(f 1+f 2) := by
    rw [show (Finset.univ : Finset (Fin 3))={0,1,2} by decide];simp
  rw [sum,kc,Nat.add_mul] at total
  change crossCount Q S Sᶜ+(crossCount Q L Lᶜ+crossCount Q R Rᶜ)+2≤S.ncard*D+3*D at total
  rw [scost] at total
  have sideCap (A : Set X) (sub : A⊆P\{x.val}) (clA : Q.IsClique A)
      (near : ∃a∈A,Q.Adj x.val a) : A.ncard≤D-1 := by
    obtain ⟨a,ha,xa⟩ := near
    obtain ⟨u,ui,au⟩ := largest_independent_dominates Q I ind largest a (s.pOut (sub ha).1)
    exact clique_size_with_two_exits Q A clA D reg ha
      (fun hx => (sub hx).2 (by simp)) (fun hu => s.pOut (sub hu).1 ui)
      (show x.val≠u from fun e => xi (e.symm ▸ ui)) xa.symm au
  have lcap := sideCap L lsub cl nearL
  have rcap := sideCap R rsub cr nearR
  have lcost := clique_boundary_count Q L D cl (fun v _ => reg v)
  have rcost := clique_boundary_count Q R D cr (fun v _ => reg v)
  have sizes := congrArg Set.ncard parts
  rw [Set.ncard_union_eq lr] at sizes
  have remove := Set.ncard_sdiff_singleton_add_one (show x.val∈P from xp)
  change (P\{x.val}).ncard+1=P.ncard at remove
  change L.ncard+R.ncard=(P\{x.val}).ncard at sizes
  have nl := (Set.ncard_pos (Set.toFinite _)).mpr ln
  have nr := (Set.ncard_pos (Set.toFinite _)).mpr rn
  change D+1≤P.ncard at large
  have alt : (L.ncard=D-1 ∧ R.ncard=1) ∨ (R.ncard=D-1 ∧ L.ncard=1) := by
    by_cases one : L.ncard=1
    · exact Or.inr ⟨by omega,one⟩
    have two := clique_min_cost D L.ncard (by omega) lcap
    have rone : R.ncard=1 := by
      by_contra many
      have other := clique_min_cost D R.ncard (by omega) rcap
      omega
    exact Or.inl ⟨by omega,rone⟩
  have finish (A B : Set X) (clA : Q.IsClique A) (sz : A.ncard=D-1) (one : B.ncard=1)
      (disAB : Disjoint A B) (part : A∪B=P\{x.val}) (subA : A⊆P\{x.val}) (subB : B⊆P\{x.val})
      (near : ∃a∈A,Q.Adj x.val a) (nearB : ∃b∈B,Q.Adj x.val b)
      (away : ∀a∈A,∀b∈B,¬Q.Adj a b) : Nonempty (BadSingleSplit Q P x.val D) := by
    obtain ⟨b,hb,adj⟩ := nearB
    have beq : B={b} := by
      ext v; exact ⟨fun hv => Set.mem_singleton_iff.mpr
        ((Set.ncard_le_one (Set.toFinite _)).mp one.le v hv b hb),
        fun eq => (Set.mem_singleton_iff.mp eq).symm ▸ hb⟩
    exact ⟨{
      side := A
      leaf := b
      clique := clA
      order := sz
      off := fun h => (subA h).2 (by simp)
      leaf_off := by simpa using (subB hb).2
      distinct := fun h => Set.disjoint_left.mp disAB h hb
      parts := beq ▸ part
      near := near
      to_leaf := adj
      away := fun v hv => away v hv b hb
    }⟩
  rcases alt with ⟨ls,rs⟩|⟨rs,ls⟩
  · exact finish L R cl ls rs lr parts lsub rsub nearL nearR sep
  · exact finish R L cr rs ls lr.symm (by rw [Set.union_comm,parts]) rsub lsub nearR nearL
      (fun b hb a ha e => sep a ha b hb e.symm)

#print axioms split_large_bad_single_from_four
end JSP452Audit.StarHost
