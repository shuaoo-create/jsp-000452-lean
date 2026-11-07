import CrossingPositiveReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {V : Type*} [Finite V]

structure DetachedMatePair {V : Type*} (H : SimpleGraph V) where
  preferred : Set V
  companion : Set V
  singles : Set V
  apart : Disjoint preferred companion
  sp : Disjoint singles preferred
  sc : Disjoint singles companion
  cover : ∀v,v∈singles ∨ v∈companion ∨ v∈preferred
  isolated : ∀v∈singles,∀u,¬ H.Adj v u
  apart_edges : ∀v∈preferred,∀u∈companion,¬ H.Adj v u
  preferred_odd : Odd preferred.ncard
  preferred_big : 3≤preferred.ncard
  companion_odd : Odd companion.ncard
  companion_big : 3≤companion.ncard
  companion_clique : H.IsClique companion

/-- Under the detached hypothesis, two named active blocks exhaust the
active indices; all other vertices outside them are the original holes. -/
theorem actual_detached_pair (Q : SimpleGraph V) (I : Set V)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set V,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (six : 6≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching) (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p q : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set V))) (qp : q≠p)
    (bigP : 3≤(mateBlock (Q.induce Iᶜ) N p.val).ncard)
    (bigQ : 3≤(mateBlock (Q.induce Iᶜ) N q.val).ncard)
    (others : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set V)),j≠p → (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N j.val))
    (detached : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set V)),j≠p →
      ∀v∈mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N,
      ∀u∈mateBlock (Q.induce Iᶜ) N j.val,¬(Q.induce Iᶜ).Adj v u) :
    ∃ s : DetachedMatePair (Q.induce Iᶜ),
      s.preferred=mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N ∧
      s.companion=mateBlock (Q.induce Iᶜ) N q.val ∧ s.singles.ncard+3=I.ncard := by
  classical
  let H := Q.induce Iᶜ
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set V))
  let P := mateBlock H N p.val ∪ zeroMateRegion H N
  let C := mateBlock H N q.val
  let S := (N.vertsᶜ\{p.val})\{q.val}
  let A : Set J := {j | 3≤(mateBlock H N j.val).ncard}
  have cap : A.ncard≤2 := (detached_preferred_active_count Q I ind largest D six par reg N hm max gap noEx p bigP others detached).1
  have pq : p.val≠q.val := fun eq => qp (Subtype.ext eq.symm)
  have single (j:J) (jp:j≠p) (jq:j≠q) : (mateBlock H N j.val).ncard=1 := by
    have parity := Nat.odd_iff.mp (mateBlock_odd H N hm j.val j.property)
    by_contra diff
    have big : 3≤(mateBlock H N j.val).ncard := by omega
    have sub : ({j,p,q} : Set J)⊆A := by
      rintro _ (e|e|e)
      · exact e.symm ▸ (big : j∈A)
      · exact e.symm ▸ (bigP : p∈A)
      · exact (Set.mem_singleton_iff.mp e).symm ▸ (bigQ : q∈A)
    have bound := Set.ncard_le_ncard sub
    rw [Set.ncard_insert_of_notMem (by simp [jp,jq]),Set.ncard_pair qp.symm] at bound
    omega
  have count : S.ncard+3=I.ncard := by
    have first := Set.ncard_sdiff_singleton_add_one p.property
    have hq : q.val∈N.vertsᶜ\{p.val} := ⟨q.property,fun h => pq (Set.mem_singleton_iff.mp h).symm⟩
    have second := Set.ncard_sdiff_singleton_add_one hq
    change ((N.vertsᶜ\{p.val})\{q.val}).ncard+3=I.ncard
    omega
  have inS {v} (h:v∈S) : v∉N.verts ∧ v≠p.val ∧ v≠q.val := by
    simpa [S,and_assoc] using h
  have sp : Disjoint S P := by
    apply Set.disjoint_left.mpr
    intro v hv hp
    obtain ⟨hole,np,_⟩ := inS hv
    rcases hp with h|⟨_,xy,_,_⟩
    · exact Set.disjoint_left.mp (mateBlock_disjoint_other_holes H N p.val) h ⟨hole,by simpa using np⟩
    · exact hole (N.edge_vert xy)
  have sc : Disjoint S C := by
    apply Set.disjoint_left.mpr
    intro v hv hc
    obtain ⟨hole,_,nq⟩ := inS hv
    exact Set.disjoint_left.mp (mateBlock_disjoint_other_holes H N q.val) hc ⟨hole,by simpa using nq⟩
  have pc : Disjoint P C := Set.disjoint_union_left.mpr
    ⟨different_mate_blocks_disjoint H N hm max p.val q.val p.property q.property pq,
      (mate_block_disjoint_zero H N hm q.val q.property).symm⟩
  have sole {j:J} (jp:j≠p) (jq:j≠q) {v} (hv:v∈mateBlock H N j.val) : v=j.val :=
    (Set.ncard_le_one (Set.toFinite _)).mp (single j jp jq).le v hv j.val (mateBlock_self H N j.val)
  have union (v : ↥(Iᶜ : Set V)) : v∈S ∨ v∈C ∨ v∈P := by
    rcases mate_classes_cover H N hm v with ⟨u,hu,hv⟩|hz|ex
    · let j : J := ⟨u,hu⟩
      by_cases jp:j=p
      · exact Or.inr (Or.inr (Or.inl (jp ▸ (hv : v∈mateBlock H N j.val))))
      by_cases jq:j=q
      · have z : v∈mateBlock H N q.val := jq ▸ (hv : v∈mateBlock H N j.val)
        exact Or.inr (Or.inl z)
      have eq := sole jp jq hv
      have us : j.val∈S := ⟨⟨hu,fun h => jp (Subtype.ext (Set.mem_singleton_iff.mp h))⟩,
        fun h => jq (Subtype.ext (Set.mem_singleton_iff.mp h))⟩
      exact Or.inl (eq.symm ▸ us)
    · exact Or.inr (Or.inr (Or.inr hz))
    · exact (noEx ▸ ex : v∈(∅ : Set ↥(Iᶜ : Set V))).elim
  have iso (s) (hs:s∈S) (v) : ¬H.Adj s v := by
    obtain ⟨hole,np,nq⟩ := inS hs
    rcases mate_classes_cover H N hm v with ⟨u,hu,hv⟩|⟨_,_,av,_⟩|ex
    · by_cases eq : s=u
      · let j : J := ⟨s,hole⟩
        have own : v=j.val := sole (fun h => np (congrArg Subtype.val h))
          (fun h => nq (congrArg Subtype.val h)) (show v∈mateBlock H N s from eq.symm ▸ hv)
        exact fun e => e.ne own.symm
      · exact fun e => mateBlock_separated H N hm max hu v hv s ⟨hole,by simpa using eq⟩ e.symm
    · exact fun e => av s hole e.symm
    · exact (noEx ▸ ex : v∈(∅ : Set ↥(Iᶜ : Set V))).elim
  refine ⟨{
    preferred := P
    companion := C
    singles := S
    apart := pc
    sp := sp
    sc := sc
    cover := union
    isolated := iso
    apart_edges := detached q qp
    preferred_odd := preferred_region_odd H N hm p.val p.property
    preferred_big := bigP.trans (Set.ncard_le_ncard Set.subset_union_left)
    companion_odd := mateBlock_odd H N hm q.val q.property
    companion_big := bigQ
    companion_clique := others q qp
  },rfl,rfl,count⟩

#print axioms actual_detached_pair
end JSP452Audit.StarHost
