import TwinTrianglesFourRootEdges
import ExceptionalRankBudget
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- Liu's zero-reserve rank after an independent cut contradicts four
disjoint retained root edges. All vertices are original graph labels. -/
theorem twin_triangles_touch_at_most_three_roots (Q : SimpleGraph X) (I : Set X)
    (h : TwinTriangleParts Q I) (reg : ∀v,Nat.card (Q.neighborSet v)=4)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q 4=0) :
    (triangleRoots Q I h).ncard≤3 := by
  classical
  by_contra! many
  obtain ⟨a,ha,b,hb,g,hits⟩ := four_root_edges_after_two_omissions Q I h reg many
  let A := h.P∪h.C
  let K := A\{a,b}
  let Y := h.S∪{a,b}
  have ab : a≠b := h.pc.ne_of_mem ha hb
  have cutdis : Disjoint h.S ({a,b}:Set X) := by
    apply Set.disjoint_left.mpr
    rintro v hv (e|e)
    · exact Set.disjoint_left.mp h.sp hv (e.symm ▸ ha)
    · exact Set.disjoint_left.mp h.sc hv ((Set.mem_singleton_iff.mp e).symm ▸ hb)
  have price : Y.ncard=h.S.ncard+2 := by rw [show Y=h.S∪{a,b} from rfl,Set.ncard_union_eq cutdis,Set.ncard_pair ab]
  have size : A.ncard=6 := by rw [show A=h.P∪h.C from rfl,Set.ncard_union_eq h.pc,h.pSize,h.cSize]
  have outside : A⊆Iᶜ := Set.union_subset h.pOut h.cOut
  have sa : Disjoint h.S A := Set.disjoint_union_right.mpr ⟨h.sp,h.sc⟩
  have all : Iᶜ=h.S∪A := by
    ext v
    constructor
    · intro away
      rcases h.cover v with hi|s|p|c
      · exact (away hi).elim
      · exact Or.inl s
      · exact Or.inr (Or.inl p)
      · exact Or.inr (Or.inr c)
    · exact fun m => m.elim (fun s => h.sOut s) (fun w => outside w)
  have order := Set.ncard_add_ncard_compl I
  rw [all,Set.ncard_union_eq sa,size] at order
  have yOut : Y⊆Iᶜ := by
    rintro _ (s|e|e)
    · exact h.sOut s
    · exact e.symm ▸ h.pOut ha
    · exact (Set.mem_singleton_iff.mp e).symm ▸ h.cOut hb
  have nab : ¬Q.Adj a b := fun e => h.cOut hb (h.pExt a ha b e (fun hp => Set.disjoint_left.mp h.pc hp hb))
  have yi : Q.IsIndepSet Y := by
    intro u hu v hv ne edge
    rcases hu with s|ae|be
    · exact yOut hv (h.isolated u s v edge)
    · rcases hv with t|ax|bx
      · exact h.pOut ha (ae ▸ h.isolated v t u edge.symm)
      · exact ne (ae.trans ax.symm)
      · exact nab (ae ▸ (Set.mem_singleton_iff.mp bx) ▸ edge)
    · have be := Set.mem_singleton_iff.mp be
      rcases hv with t|ax|bx
      · exact h.cOut hb (be ▸ h.isolated v t u edge.symm)
      · exact nab (be ▸ ax ▸ edge.symm)
      · exact ne (be.trans (Set.mem_singleton_iff.mp bx).symm)
  have rank := (zero_reserve_independent_cut Q 4 (by decide) reg crit zero Y ⟨a,Or.inr (Or.inl rfl)⟩ yi).2.1
  have ord := factorCritical_order_rank Q crit a
  have count := h.count
  have upper : matchingEdges (Q.induce Yᶜ)=3 := by omega
  have kept (w:K) : w.val∉Y := by
    rintro (s|pair)
    · exact Set.disjoint_left.mp sa s w.property.1
    · exact w.property.2 pair
  have rkept (v:K) : g v∉Y := fun m => yOut m (hits v).1
  let l : K ↪ ↥(Yᶜ : Set X) := ⟨fun v => ⟨v.val,kept v⟩,fun _ _ e => Subtype.ext (congrArg (fun z : ↥(Yᶜ : Set X) => z.val) e)⟩
  let r : K ↪ ↥(Yᶜ : Set X) := ⟨fun v => ⟨g v,rkept v⟩,fun _ _ e => g.injective (congrArg Subtype.val e)⟩
  have apart : Disjoint (Set.range l) (Set.range r) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨i,rfl⟩ ⟨j,e⟩
    have v : g j=i.val := congrArg Subtype.val e
    exact outside i.property.1 (v ▸ (hits j).1)
  have low := even_clique_and_edge_family_rank (Q.induce Yᶜ) ∅ (by simp) (by simp)
    l r (fun i => (hits i).2) apart (by simp)
  have inc : ({a,b}:Set X)⊆A := Set.insert_subset (Or.inl ha) (Set.singleton_subset_iff.mpr (Or.inr hb))
  have rm := Set.ncard_sdiff_add_ncard_of_subset inc
  change K.ncard+({a,b}:Set X).ncard=A.ncard at rm
  rw [Set.ncard_pair ab,size] at rm
  rw [Set.ncard_empty,zero_add,Nat.card_coe_set_eq,upper] at low
  omega

#print axioms twin_triangles_touch_at_most_three_roots
end JSP452Audit.StarHost
