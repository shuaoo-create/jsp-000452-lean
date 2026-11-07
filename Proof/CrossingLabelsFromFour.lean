import CrossingShapeFromFour
import OriginalThreePathShape
namespace JSP452Audit.StarHost
open SimpleGraph
variable {V : Type*} [Finite V]

/-- Obtain the actual labelled shape, including the count and isolation of all
other uncovered vertices of the same maximum matching. -/
theorem original_crossing_shape_from_four (Q : SimpleGraph V) (I : Set V)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set V,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (N : (Q.induce Iᶜ).Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges (Q.induce Iᶜ))
    (gap : N.vertsᶜ.ncard+1=I.ncard) (noEx : exceptionalMateRegion (Q.induce Iᶜ) N=∅)
    (p q : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set V))) (qp : q≠p)
    (conn : ((Q.induce Iᶜ).induce (mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N)).Preconnected)
    (others : ∀j : ↥(N.vertsᶜ : Set ↥(Iᶜ : Set V)), j≠p → (Q.induce Iᶜ).IsClique (mateBlock (Q.induce Iᶜ) N j.val))
    (x : ↥(mateBlock (Q.induce Iᶜ) N p.val∪zeroMateRegion (Q.induce Iᶜ) N))
    (y : mateBlock (Q.induce Iᶜ) N q.val) (edge : (Q.induce Iᶜ).Adj x.val y.val) :
    ∃ frame : ThreePathShape (Q.induce Iᶜ) D, frame.singles.ncard+3=I.ncard ∧
      frame.companion=mateBlock (Q.induce Iᶜ) N q.val ∧ frame.pivot=x.val := by
  classical
  let H := Q.induce Iᶜ
  let P := mateBlock H N p.val∪zeroMateRegion H N
  let C := mateBlock H N q.val
  let S := (N.vertsᶜ\{p.val})\{q.val}
  let J := ↥(N.vertsᶜ : Set ↥(Iᶜ : Set V))
  have pq : p.val≠q.val := fun eq => qp (Subtype.ext eq.symm)
  obtain ⟨l,r,lr,lx,rx,path,xl,xr,apart,order,single⟩ :=
    crossing_forces_three_path_from_four Q I ind largest D four par reg N hm max gap noEx p q qp conn others x y edge
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
        exact fun edge => edge.ne own.symm
      · exact fun edge => mateBlock_separated H N hm max hu v hv s ⟨hole,by simpa using eq⟩ edge.symm
    · exact fun edge => av s hole edge.symm
    · exact (noEx ▸ ex : v∈(∅ : Set ↥(Iᶜ : Set V))).elim
  have limit (T : Set ↥(Iᶜ : Set V)) (si : H.IsIndepSet T) : T.ncard≤N.vertsᶜ.ncard+1 := by
    have imageInd : Q.IsIndepSet (Subtype.val '' T) := by
      rintro _ ⟨u,hu,rfl⟩ _ ⟨v,hv,rfl⟩ ne edge
      exact si hu hv (fun eq => ne (congrArg Subtype.val eq)) edge
    have cap := largest _ imageInd
    rwa [Set.ncard_image_of_injective _ Subtype.val_injective,←gap] at cap
  have noC {v} (vp:v∈P) (nx:v≠x.val) {b} (bc:b∈C) (adj:H.Adj v b) : False := by
    have eq := crossings_share_preferred_endpoint H N hm max p.val p.property conn limit q.val q.val
      q.property q.property pq pq (others q qp) (others q qp) x ⟨v,vp⟩ y ⟨b,bc⟩ edge adj
    exact nx (congrArg Subtype.val eq)
  have hl : l∈P := by rw [show P={x.val,l,r} from path];simp
  have hr : r∈P := by rw [show P={x.val,l,r} from path];simp
  have leaf {v t : ↥(Iᶜ : Set V)} (vp : v∈P) (nx : v≠x.val) (dx : H.Adj x.val v)
      (bad : ¬H.Adj v t) (form : P={x.val,v,t}) : H.neighborSet v={x.val} := by
    ext z
    constructor
    · intro vz
      rcases union z with hs|hc|hp
      · exact (iso z hs v vz.symm).elim
      · exact (noC vp nx hc vz).elim
      · rw [form] at hp
        simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hp
        rcases hp with eq|eq|eq
        · exact Set.mem_singleton_iff.mpr eq
        · exact ((show H.Adj v z from vz).ne eq.symm).elim
        · exact (bad (eq ▸ vz)).elim
    · intro h;exact (Set.mem_singleton_iff.mp h).symm ▸ dx.symm
  refine ⟨{
    singles := S
    companion := C
    pivot := x.val
    left := l
    right := r
    different := lr
    left_off := lx
    right_off := rx
    clean := sc
    path_free := ?_
    cover := ?_
    isolated := iso
    left_neighbors := leaf hl lx xl apart path
    right_neighbors := leaf hr rx xr (fun h => apart h.symm)
      (by rw [show P={x.val,l,r} from path,Set.pair_comm l r])
    clique := others q qp
    clique_order := order
  },count,rfl,rfl⟩
  · intro v hv
    have vp : v∈P := (show P={x.val,l,r} from path).symm ▸ hv
    exact ⟨fun hs => Set.disjoint_left.mp sp hs vp,fun hc => Set.disjoint_left.mp pc vp hc⟩
  · intro v
    rcases union v with hs|hc|hp
    · exact Or.inl hs
    · exact Or.inr (Or.inl hc)
    · rw [show P={x.val,l,r} from path] at hp
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using Or.inr (Or.inr hp)

#print axioms original_crossing_shape_from_four
end JSP452Audit.StarHost
