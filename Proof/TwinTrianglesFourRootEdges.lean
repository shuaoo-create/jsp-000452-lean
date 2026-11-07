import OriginalTwinTriangles
import TwoTripleRootAssignment
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

def triangleRoots (Q : SimpleGraph X) (I : Set X) (h : TwinTriangleParts Q I) : Set X :=
  {r | r∈I ∧ ∃v∈h.P∪h.C,Q.Adj v r}

private theorem omit_one_per_colour {L R : Type*} (A : Set L) (nonempty : A.Nonempty)
    (f : L→R⊕Bool) (inj : Function.Injective f) (b : Bool)
    (only : ∀x∈A,∀c,f x=.inr c → c=b) :
    ∃a∈A,∀x∈A,x≠a → ∃r,f x=.inl r := by
  classical
  by_cases dummy : ∃x∈A,f x=.inr b
  · obtain ⟨a,ha,hit⟩ := dummy
    refine ⟨a,ha,?_⟩
    intro x hx ne
    cases e : f x with
    | inl r => exact ⟨r,rfl⟩
    | inr c => exact (ne (inj (e.trans ((only x hx c e) ▸ hit.symm)))).elim
  obtain ⟨a,ha⟩ := nonempty
  refine ⟨a,ha,?_⟩
  intro x hx _
  cases e : f x with
  | inl r => exact ⟨r,rfl⟩
  | inr c => exact (dummy ⟨x,hx,(only x hx c e) ▸ e⟩).elim

/-- At least four real roots yield two distinct retained points per triangle,
each assigned a distinct real neighbouring root in the original graph. -/
theorem four_root_edges_after_two_omissions (Q : SimpleGraph X) (I : Set X)
    (h : TwinTriangleParts Q I) (reg : ∀v,Nat.card (Q.neighborSet v)=4)
    (many : 4≤(triangleRoots Q I h).ncard) :
    ∃a∈h.P,∃b∈h.C,∃g : ↥((h.P∪h.C)\{a,b}) ↪ X,
      ∀v,g v∈I ∧ Q.Adj v.val (g v) := by
  classical
  let _ := Fintype.ofFinite X
  let L := ↥(h.P∪h.C)
  let colour (v:L) := if v.val∈h.P then true else false
  let adj (v:L) := (Q.neighborSet v.val∩I).toFinset
  have six : Fintype.card L=6 := by
    rw [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq,Set.ncard_union_eq h.pc,h.pSize,h.cSize]
  have subset_size (T : Finset L) (A : Set X) (inc : ∀v∈T,v.val∈A) : T.card≤A.ncard := by
    let f (v : ↥T) : A := ⟨v.val.val,inc v.val v.property⟩
    have card := Nat.card_le_card_of_injective f (fun a b eq => Subtype.ext (Subtype.ext (congrArg (fun z : A => z.val) eq)))
    simpa only [Nat.card_eq_fintype_card (α := ↥T),Fintype.card_coe,Nat.card_coe_set_eq] using card
  have triple (b : Bool) : (Finset.univ.filter (fun x => colour x=b)).card≤3 := by
    cases b with
    | false =>
      rw [←h.cSize];apply subset_size
      intro v hv
      have no : v.val∉h.P := by simpa [colour] using (Finset.mem_filter.mp hv).2
      exact v.property.resolve_left no
    | true =>
      rw [←h.pSize];apply subset_size
      intro v hv
      simpa [colour] using (Finset.mem_filter.mp hv).2
  have two (v:L) : (adj v).card=2 := by
    change (Q.neighborSet v.val∩I).toFinset.card=2
    rw [←Set.ncard_eq_toFinset_card']
    rcases v.property with hp|hc
    · exact twin_triangle_two_root_neighbors Q I h.P h.pSize h.pClique h.pOut h.pExt reg v.val hp
    · exact twin_triangle_two_root_neighbors Q I h.C h.cSize h.cClique h.cOut h.cExt reg v.val hc
  have cap (r : X) : (Finset.univ.filter (fun v => r∈adj v)).card≤4 := by
    have bound := subset_size (Finset.univ.filter (fun v => r∈adj v)) (Q.neighborSet r) (by
      intro v hv
      have ok : r∈Q.neighborSet v.val∩I := Set.mem_toFinset.mp (Finset.mem_filter.mp hv).2
      exact (show Q.Adj v.val r from ok.1).symm)
    rwa [←Nat.card_coe_set_eq,reg] at bound
  have union_eq : (↑(Finset.univ.biUnion adj) : Set X)=triangleRoots Q I h := by
    ext r
    constructor
    · intro m
      obtain ⟨v,_,real⟩ := Finset.mem_biUnion.mp m
      have ok := Set.mem_toFinset.mp real
      exact ⟨ok.2,v.val,v.property,ok.1⟩
    · rintro ⟨ri,v,hv,edge⟩
      exact Finset.mem_biUnion.mpr ⟨⟨v,hv⟩,Finset.mem_univ _,Set.mem_toFinset.mpr ⟨edge,ri⟩⟩
  have total : 4≤(Finset.univ.biUnion adj).card := by rwa [←Set.ncard_coe_finset,union_eq]
  obtain ⟨f,inj,hit,only⟩ := two_triples_distinct_assignments colour adj six triple two cap total
  let A : Set L := {v | v.val∈h.P}
  let B : Set L := {v | v.val∈h.C}
  obtain ⟨p,hp⟩ := (Set.ncard_pos (Set.toFinite h.P)).mp (show 0<h.P.ncard by rw [h.pSize];decide)
  obtain ⟨c,hc⟩ := (Set.ncard_pos (Set.toFinite h.C)).mp (show 0<h.C.ncard by rw [h.cSize];decide)
  obtain ⟨a,ha,arest⟩ := omit_one_per_colour A ⟨⟨p,Or.inl hp⟩,hp⟩ f inj true (by
    intro v hv t eq;rw [only v t eq];simp [colour,(show v.val∈h.P from hv)])
  obtain ⟨b,hb,brest⟩ := omit_one_per_colour B ⟨⟨c,Or.inr hc⟩,hc⟩ f inj false (by
    intro v hv t eq;rw [only v t eq];simp only [colour,ite_eq_right_iff];intro hp
    exact (Set.disjoint_left.mp h.pc hp (show v.val∈h.C from hv)).elim)
  let K := (h.P∪h.C)\{a.val,b.val}
  let pack (v : K) : L := ⟨v.val,v.property.1⟩
  have real (v : K) : ∃r,f (pack v)=.inl r := by
    rcases v.property.1 with ap|bc
    · exact arest (pack v) ap (fun eq => v.property.2 (Or.inl (congrArg Subtype.val eq)))
    · exact brest (pack v) bc (fun eq => v.property.2 (Or.inr (Set.mem_singleton_iff.mpr (congrArg Subtype.val eq))))
  let g (v:K) := (real v).choose
  have assigned (v:K) : f (pack v)=.inl (g v) := (real v).choose_spec
  refine ⟨a.val,ha,b.val,hb,⟨g,?_⟩,?_⟩
  · intro v w eq
    have same : pack v=pack w := inj ((assigned v).trans ((congrArg Sum.inl eq).trans (assigned w).symm))
    exact Subtype.ext (congrArg (fun z : L => z.val) same)
  · intro v
    have ok := Set.mem_toFinset.mp (hit (pack v) (g v) (assigned v))
    exact ⟨ok.2,ok.1⟩

#print axioms four_root_edges_after_two_omissions
end JSP452Audit.StarHost
