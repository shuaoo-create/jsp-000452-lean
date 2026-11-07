import NearCliqueBipartiteCut
import LargeCriticalPreferred
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

private theorem two_singletons_common_root (Q : SimpleGraph X) (I : Set X)
    (D : ℕ) (six : 6≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (s : OnePreferredPart Q I) (many : 3≤I.ncard) :
    ∃i∈I,∃a∈s.singles,∃b∈s.singles,a≠b ∧ Q.Adj i a ∧ Q.Adj i b := by
  classical
  let _ := Fintype.ofFinite I
  have dI := single_part_root_degree Q I D reg s many
  have count := s.count
  have cost : crossCount Q I s.singles=s.singles.ncard*D := uniform_cross_count Q s.singles I D (by
    intro v hv;rw [Set.inter_eq_left.mpr (show Q.neighborSet v⊆I from s.isolated v hv),
      ←Nat.card_coe_set_eq,reg])
  have large : ∃v:I,2≤(Q.neighborSet v.val∩s.singles).ncard := by
    by_contra! small
    rw [crossCount_eq_neighbor_sum] at cost
    have bound := Finset.sum_le_sum (s:=(Finset.univ : Finset I)) (fun v _ =>
      (show (Q.neighborSet v.val∩s.singles).ncard≤1 by have h:=small v;omega))
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one,Finset.card_univ,←Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq,cost] at bound
    change s.singles.ncard*D≤I.ncard at bound
    have four : 4≤s.singles.ncard := by omega
    have mult := Nat.mul_le_mul_left s.singles.ncard (show 2≤D by omega)
    omega
  obtain ⟨i,h⟩ := large
  obtain ⟨a,b,⟨ia,sa⟩,⟨ib,sb⟩,ne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp h
  exact ⟨i.val,i.property,a,sa,b,sb,ne,ia,ib⟩

omit [Nonempty X] in
private theorem degree_loss_two (Q : SimpleGraph X) (U : Set X) (v : ↥(Uᶜ : Set X))
    (a b:X) (au:a∈U) (bu:b∈U) (ne:a≠b) (va:Q.Adj v.val a) (vb:Q.Adj v.val b)
    (D : ℕ) (reg : Nat.card (Q.neighborSet v.val)=D) :
    Nat.card ((Q.induce Uᶜ).neighborSet v)≤D-2 := by
  let N := Q.neighborSet v.val
  have ds : Disjoint (N∩Uᶜ) ({a,b} : Set X) := by
    apply Set.disjoint_left.mpr
    rintro _ hv (he|he)
    · exact hv.2 (he.symm ▸ au)
    · exact hv.2 ((Set.mem_singleton_iff.mp he).symm ▸ bu)
  have sub : (N∩Uᶜ)∪{a,b}⊆N := by
    rintro _ (h|ha|hb)
    · exact h.1
    · exact ha.symm ▸ va
    · exact (Set.mem_singleton_iff.mp hb).symm ▸ vb
  have bound := Set.ncard_le_ncard sub
  rw [Set.ncard_union_eq ds,Set.ncard_pair ne] at bound
  have cardN : N.ncard=D := (Nat.card_coe_set_eq N).symm.trans reg
  rw [cardN] at bound
  rw [induced_degree_intersection]
  change (N∩Uᶜ).ncard≤D-2
  omega

/-- When the sole nontrivial part has at most D−1 labels, the actual
degree-(D−1) layer can be paid with |I|−1 deletions. -/
theorem small_single_part_witness (Q : SimpleGraph X) (I : Set X) (ind : Q.IsIndepSet I)
    (many : 3≤I.ncard) (D : ℕ) (six : 6≤D) (par : Even D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (s : OnePreferredPart Q I)
    (short : s.preferred.ncard≤D-1) :
    ∃U : Set X,U.ncard+1=I.ncard ∧ admits_matching_remainder (Q.induce Uᶜ) (D-1) := by
  classical
  let P := s.preferred
  let S := s.singles
  have cost := (one_preferred_exact_boundary Q I ind D reg s).1
  have branches := low_boundary_small_region Q P D six par s.odd s.big short (fun v _ => reg v) cost.le
  have almost : (Q.induce P)ᶜ.edgeSet.ncard≤1 := by rcases branches with ⟨_,_,h⟩|⟨_,h⟩ <;> omega
  obtain ⟨a,ha,b,hb,ab,adjBoth⟩ := two_clique_deletions Q P s.big almost
  obtain ⟨i,hi,t,ht,u,hu,tu,it,iu⟩ := two_singletons_common_root Q I D six reg s many
  let L := S\{t,u}
  let U := L∪{i,a,b}
  have iU : i∈U := Or.inr (by simp)
  have aU : a∈U := Or.inr (by simp)
  have bU : b∈U := Or.inr (by simp)
  have ip : i∉P := fun hp => s.pOut hp hi
  have dis : Disjoint L ({i,a,b} : Set X) := by
    apply Set.disjoint_left.mpr
    rintro v h (eq|eq|eq)
    · exact s.sOut h.1 (eq.symm ▸ hi)
    · exact Set.disjoint_left.mp s.dis h.1 (eq.symm ▸ ha)
    · exact Set.disjoint_left.mp s.dis h.1 ((Set.mem_singleton_iff.mp eq).symm ▸ hb)
  have paid : U.ncard+1=I.ncard := by
    have inc : ({t,u} : Set X)⊆S := Set.insert_subset ht (Set.singleton_subset_iff.mpr hu)
    have loss := Set.ncard_sdiff_add_ncard_of_subset inc
    rw [Set.ncard_pair tu] at loss
    change L.ncard+2=S.ncard at loss
    have ia : i≠a := fun eq => ip (eq.symm ▸ ha)
    have ib : i≠b := fun eq => ip (eq.symm ▸ hb)
    have c := s.count
    change S.ncard+2=I.ncard at c
    change (L∪{i,a,b}).ncard+1=I.ncard
    rw [Set.ncard_union_eq dis,Set.ncard_insert_of_notMem (by simp [ia,ib]),Set.ncard_pair ab]
    omega
  let K := Q.induce Uᶜ
  let R : Set ↥(Uᶜ : Set X) := {v | v.val∈I}
  let A := ({t,u} : Set X)∪(P\{a,b})
  have acard : A.ncard≤P.ncard := by
    have sub : ({a,b} : Set X)⊆P := Set.insert_subset ha (Set.singleton_subset_iff.mpr hb)
    have loss := Set.ncard_sdiff_add_ncard_of_subset sub
    have cap := Set.ncard_union_le ({t,u} : Set X) (P\{a,b})
    rw [Set.ncard_pair tu] at cap; rw [Set.ncard_pair ab] at loss
    change ({t,u}∪(P\{a,b}) : Set X).ncard≤P.ncard;omega
  have classify (v:↥(Uᶜ : Set X)) : v.val∈I ∨ v.val=t ∨ v.val=u ∨ v.val∈P\{a,b} := by
    rcases s.cover v.val with h|h|h
    · exact Or.inl h
    · by_cases eq : v.val=t
      · exact Or.inr (Or.inl eq)
      by_cases other : v.val=u
      · exact Or.inr (Or.inr (Or.inl other))
      exact (v.property (Or.inl ⟨h,by simp [eq,other]⟩)).elim
    · refine Or.inr (Or.inr (Or.inr ⟨h,?_⟩))
      intro inside
      exact v.property (Or.inr (Or.inr inside))
  have rootBound (v:↥(Uᶜ : Set X)) (vi:v.val∈I) : Nat.card (K.neighborSet v)≤D-1 := by
    have sub : Q.neighborSet v.val∩Uᶜ⊆A := by
      rintro w ⟨vw,wu⟩
      rcases classify ⟨w,wu⟩ with wi|eq|eq|wp
      · exact (ind vi wi (show Q.Adj v.val w from vw).ne vw).elim
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inl eq))
      · exact Or.inl (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr eq)))
      · exact Or.inr wp
    rw [show K=Q.induce Uᶜ from rfl,induced_degree_intersection]
    exact (Set.ncard_le_ncard sub).trans (acard.trans short)
  have singleBound (v:↥(Uᶜ : Set X)) (iv:Q.Adj i v.val) : Nat.card (K.neighborSet v)≤D-1 := by
    rw [show K=Q.induce Uᶜ from rfl,induced_degree_intersection]
    have strict : Q.neighborSet v.val∩Uᶜ ⊂ Q.neighborSet v.val :=
      ⟨Set.inter_subset_left,fun incl => (incl iv.symm).2 iU⟩
    have h := Set.ncard_lt_ncard strict
    rw [←Nat.card_coe_set_eq (Q.neighborSet v.val),reg] at h;omega
  have pBound (v:↥(Uᶜ : Set X)) (h:v.val∈P\{a,b}) : Nat.card (K.neighborSet v)≤D-2 := by
    have edges := adjBoth v.val h.1 (fun eq => h.2 (Or.inl eq))
      (fun eq => h.2 (Or.inr (Set.mem_singleton_iff.mpr eq)))
    exact degree_loss_two Q U v a b aU bU ab edges.1 edges.2 D (reg _)
  refine ⟨U,paid,remainder_via_bipartite_cut K R (D-1) (by omega) ?_ ?_⟩
  · intro v
    rcases classify v with vi|eq|eq|h
    · exact rootBound v vi
    · exact singleBound v (show Q.Adj i v.val from eq.symm ▸ it)
    · exact singleBound v (show Q.Adj i v.val from eq.symm ▸ iu)
    · have bound := pBound v h;omega
  · intro v full w edge
    rcases classify v with vi|eq|eq|h
    · exact iff_of_true vi (fun wi => ind vi wi (show Q.Adj v.val w.val from edge).ne edge)
    · have wi : w∈R := s.isolated _ ht w.val (show Q.Adj t w.val from eq ▸ (show Q.Adj v.val w.val from edge))
      exact iff_of_false (fun h => s.sOut ht (eq ▸ h)) (fun h => h wi)
    · have wi : w∈R := s.isolated _ hu w.val (show Q.Adj u w.val from eq ▸ (show Q.Adj v.val w.val from edge))
      exact iff_of_false (fun h => s.sOut hu (eq ▸ h)) (fun h => h wi)
    · have bound := pBound v h;omega

#print axioms small_single_part_witness
end JSP452Audit.StarHost
