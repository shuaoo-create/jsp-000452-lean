import OneFullRootMatching
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

private theorem degree_loss_set (Q : SimpleGraph X) (U : Set X) (v : ↥(Uᶜ : Set X)) (A : Set X)
    (removed : A⊆U) (neighbors : A⊆Q.neighborSet v.val) (D : ℕ) (reg : Nat.card (Q.neighborSet v.val)=D) :
    Nat.card ((Q.induce Uᶜ).neighborSet v)+A.ncard≤D := by
  let N := Q.neighborSet v.val
  have dis : Disjoint (N∩Uᶜ) A := Set.disjoint_left.mpr (fun _ h k => h.2 (removed k))
  have sub : (N∩Uᶜ)∪A⊆N := Set.union_subset Set.inter_subset_left neighbors
  have bound := Set.ncard_le_ncard sub
  rw [Set.ncard_union_eq dis,←Nat.card_coe_set_eq N,reg] at bound
  rw [induced_degree_intersection];exact bound

/-- After selecting a clique point adjacent to both possible roots, remove it,
the pivot, and all but two of the pivot's singleton neighbours. -/
theorem large_exceptional_deletion (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (largest : ∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard) (D : ℕ) (four : 4≤D)
    (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (zero : baseReserve Q D=0) (s : HeavyCliqueFrame Q I D) :
    ∃U : Set X,U.ncard+1=I.ncard ∧ admits_matching_remainder (Q.induce Uᶜ) (D-1) := by
  classical
  obtain ⟨r,ri,t,ti,rt,ar,z,zc,zr,zt,only⟩ := only_two_roots_touch_clique Q I ind largest D four par reg crit zero s
  obtain ⟨u,us,v,vs,uv,au,av⟩ := s.two
  let C := s.cliquePart
  let S := s.singles
  let L := S\{u,v}
  let U := L∪{s.pivot,z}
  have az : s.pivot≠z := fun eq => s.ac (eq.symm ▸ zc)
  have aU : s.pivot∈U := Or.inr (Or.inl rfl)
  have zU : z∈U := Or.inr (Or.inr (Set.mem_singleton z))
  have left (w:X) (sw:w∈S) (pair:w=u ∨ w=v) : w∉U := by
    rintro (h|eq|eq)
    · exact h.2 (pair.elim Or.inl (fun same => Or.inr (Set.mem_singleton_iff.mpr same)))
    · exact s.as_ (eq ▸ sw)
    · exact Set.disjoint_left.mp s.dis ((Set.mem_singleton_iff.mp eq) ▸ sw) zc
  have roots (w:X) (wi:w∈I) : w∉U := by
    rintro (h|eq|eq)
    · exact s.sOut h.1 wi
    · exact s.ai (eq ▸ wi)
    · exact s.cOut zc ((Set.mem_singleton_iff.mp eq) ▸ wi)
  have cliqueKeeps {w} (wc:w∈C) (wz:w≠z) : w∉U := by
    rintro (h|eq|eq)
    · exact Set.disjoint_left.mp s.dis h.1 wc
    · exact s.ac (eq ▸ wc)
    · exact wz (Set.mem_singleton_iff.mp eq)
  have sep : Disjoint L ({s.pivot,z}:Set X) := by
    apply Set.disjoint_left.mpr
    rintro w hw (eq|eq)
    · exact s.as_ (eq ▸ hw.1)
    · exact Set.disjoint_left.mp s.dis ((Set.mem_singleton_iff.mp eq) ▸ hw.1) zc
  have card : U.ncard+1=I.ncard := by
    have rm := Set.ncard_sdiff_add_ncard_of_subset (show ({u,v}:Set X)⊆S from Set.insert_subset us (Set.singleton_subset_iff.mpr vs))
    rw [Set.ncard_pair uv] at rm
    change L.ncard+2=S.ncard at rm
    have size : S.ncard+1=I.ncard := s.count
    rw [show U=L∪{s.pivot,z} from rfl,Set.ncard_union_eq sep,Set.ncard_pair az];omega
  let H := Q.induce Uᶜ
  let R : Set ↥(Uᶜ : Set X) := {w | w.val∈I}
  let K : Set ↥(Uᶜ : Set X) := {w | w.val∈C}
  let l : ↥(Uᶜ : Set X) := ⟨u,left u us (Or.inl rfl)⟩
  let m : ↥(Uᶜ : Set X) := ⟨v,left v vs (Or.inr rfl)⟩
  let target : ↥(Uᶜ : Set X) := ⟨t,roots t ti⟩
  have shape (w : ↥(Uᶜ : Set X)) : w.val∈I ∨ w=l ∨ w=m ∨ w∈K := by
    rcases s.cover w.val with wi|ea|ws|wc
    · exact Or.inl wi
    · exact (w.property (ea.symm ▸ aU)).elim
    · by_cases same:w.val=u
      · exact Or.inr (Or.inl (Subtype.ext same))
      by_cases other:w.val=v
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext other)))
      exact (w.property (Or.inl ⟨ws,by simp [same,other]⟩)).elim
    · exact Or.inr (Or.inr (Or.inr wc))
  have order : K.ncard=D-2 := by
    have image : Subtype.val '' K=C\{z} := by
      ext w
      constructor
      · rintro ⟨p,hp,rfl⟩;exact ⟨hp,fun eq => p.property ((Set.mem_singleton_iff.mp eq).symm ▸ zU)⟩
      · rintro ⟨wc,ne⟩;exact ⟨⟨w,cliqueKeeps wc (by simpa using ne)⟩,wc,rfl⟩
    have eq := (Set.ncard_image_of_injective K Subtype.val_injective).symm.trans (congrArg Set.ncard image)
    have rm := Set.ncard_sdiff_singleton_add_one (show z∈C from zc)
    have size : C.ncard=D-1 := s.order
    omega
  have evenK : Even K.ncard := by have p := Nat.even_iff.mp par;rw [Nat.even_iff,order];omega
  have one (w : ↥(Uᶜ : Set X)) (v0:X) (out:v0∈U) (edge:Q.Adj w.val v0) :
      Nat.card (H.neighborSet w)≤D-1 := by
    have bound := degree_loss_set Q U w {v0} (Set.singleton_subset_iff.mpr out) (Set.singleton_subset_iff.mpr edge) D (reg _)
    rw [Set.ncard_singleton] at bound
    change Nat.card (H.neighborSet w)+1≤D at bound
    omega
  have firstRoot (w : ↥(Uᶜ : Set X)) (wr:w.val=r) : Nat.card (H.neighborSet w)≤D-2 := by
    have rem : ({s.pivot,z}:Set X)⊆U := Set.insert_subset aU (Set.singleton_subset_iff.mpr zU)
    have adj : ({s.pivot,z}:Set X)⊆Q.neighborSet w.val := by
      rintro p (e|e)
      · exact (show Q.Adj w.val p from wr.symm ▸ e.symm ▸ ar.symm)
      · exact (show Q.Adj w.val p from wr.symm ▸ (Set.mem_singleton_iff.mp e).symm ▸ zr.symm)
    have bound := degree_loss_set Q U w _ rem adj D (reg _)
    rw [Set.ncard_pair az] at bound
    change Nat.card (H.neighborSet w)+2≤D at bound;omega
  have otherRoot (w : ↥(Uᶜ : Set X)) (wi:w.val∈I) (wr:w.val≠r) (wt:w.val≠t) :
      Nat.card (H.neighborSet w)≤2 := by
    have sub : H.neighborSet w ⊆ {l,m} := by
      intro v0 edge
      rcases shape v0 with vi|eq|eq|cc
      · exact (ind wi vi (show Q.Adj w.val v0.val from edge).ne edge).elim
      · exact Or.inl eq
      · exact Or.inr (Set.mem_singleton_iff.mpr eq)
      · exact ((only v0.val cc w.val wi (show Q.Adj w.val v0.val from edge).symm).elim wr wt).elim
    have bnd := Set.ncard_le_ncard sub
    rw [Set.ncard_pair (show l≠m from fun eq => uv (congrArg Subtype.val eq)),←Nat.card_coe_set_eq] at bnd;exact bnd
  have cap (w:↥(Uᶜ : Set X)) : Nat.card (H.neighborSet w)≤D-1 := by
    rcases shape w with wi|eq|eq|cc
    · by_cases wr:w.val=r
      · have bnd := firstRoot w wr;omega
      by_cases wt:w.val=t
      · exact one w z zU (show Q.Adj w.val z from wt.symm ▸ zt.symm)
      have bnd := otherRoot w wi wr wt;omega
    · subst w;exact one l s.pivot aU au.symm
    · subst w;exact one m s.pivot aU av.symm
    · exact one w z zU (s.clique cc zc (fun eq => w.property (eq.symm ▸ zU)))
  have full (w:↥(Uᶜ : Set X)) (h:Nat.card (H.neighborSet w)=D-1) : w∈K ∨ w=l ∨ w=m ∨ w=target := by
    rcases shape w with wi|eq|eq|cc
    · by_cases wr:w.val=r
      · have bnd := firstRoot w wr;omega
      by_cases wt:w.val=t
      · exact Or.inr (Or.inr (Or.inr (Subtype.ext wt)))
      have bnd := otherRoot w wi wr wt;omega
    · exact Or.inr (Or.inl eq)
    · exact Or.inr (Or.inr (Or.inl eq))
    · exact Or.inl cc
  have hit (fullT : Nat.card (H.neighborSet target)=D-1) : H.Adj l target ∨ H.Adj m target := by
    by_contra! none
    have sub : H.neighborSet target⊆K := by
      intro w edge
      rcases shape w with wi|h|h|cc
      · exact (ind ti wi (show Q.Adj t w.val from edge).ne edge).elim
      · exact (none.1 (h ▸ (show H.Adj w target from edge.symm))).elim
      · exact (none.2 (h ▸ (show H.Adj w target from edge.symm))).elim
      · exact cc
    have bnd := Set.ncard_le_ncard sub
    rw [←Nat.card_coe_set_eq (H.neighborSet target),fullT,order] at bnd;omega
  have choices (p : ↥(Uᶜ : Set X)) (ps:p.val∈S) (ap : Q.Adj s.pivot p.val) (avoid:↥(Uᶜ : Set X)) :
      ∃w∈R,w≠avoid ∧ H.Adj p w := by
    have eq : Q.neighborSet p.val=insert s.pivot (Q.neighborSet p.val∩I) := by
      ext w
      constructor
      · intro edge
        rcases s.singleEdges p.val ps w edge with wi|eq
        · exact Or.inr ⟨edge,wi⟩
        · exact Or.inl eq
      · rintro (eq|h)
        · exact (show Q.Adj p.val w from eq.symm ▸ ap.symm)
        · exact h.1
    have size := Nat.card_coe_set_eq (Q.neighborSet p.val)
    rw [reg,eq,Set.ncard_insert_of_notMem (fun h => s.ai h.2)] at size
    obtain ⟨w,⟨edge,wi⟩,ne⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
      (show ({avoid.val}:Set X).ncard<(Q.neighborSet p.val∩I).ncard by rw [Set.ncard_singleton];omega)
    exact ⟨⟨w,roots w wi⟩,wi,fun h => ne (Set.mem_singleton_iff.mpr (congrArg Subtype.val h)),edge⟩
  have dis : Disjoint R K := Set.disjoint_left.mpr (fun w wi wc => s.cOut wc wi)
  have cl : H.IsClique K := fun {x} hx {y} hy ne => s.clique hx hy (fun eq => ne (Subtype.ext eq))
  exact ⟨U,card,one_high_root_remainder H R K l m target D four (fun eq => uv (congrArg Subtype.val eq))
    (s.sOut us) (s.sOut vs) (fun h => Set.disjoint_left.mp s.dis us h) (fun h => Set.disjoint_left.mp s.dis vs h)
    ti dis cl evenK cap full hit (choices l us au) (choices m vs av)⟩

#print axioms large_exceptional_deletion
end JSP452Audit.StarHost
