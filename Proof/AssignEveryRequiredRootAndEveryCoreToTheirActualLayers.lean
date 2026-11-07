import DecomposePartialOriginalSlotsWithoutChangingAnyAssignedPair
namespace JSP452Audit.StarHost
open SimpleGraph
universe u v
variable {R:Type u} {C:Type v}

def rootEndpointBin (w:R→ℕ) {k:ℕ} (live:0<k) (x:RootSlots w) : (R⊕RootSlots w)×Fin k :=
  if small:x.2.val<k then (.inl x.1,⟨x.2.val,small⟩) else (.inr x,⟨0,live⟩)

theorem root_endpoint_bin_injective (w:R→ℕ) {k:ℕ} (live:0<k) : Function.Injective (rootEndpointBin w live) := by
  rintro ⟨r,i⟩ ⟨s,j⟩ eq
  by_cases x:i.val<k <;> by_cases y:j.val<k
  · have root := congrArg (fun z:(R⊕RootSlots w)×Fin k => z.1) eq
    have slot := congrArg (fun z:(R⊕RootSlots w)×Fin k => z.2.val) eq
    simp only [rootEndpointBin,dif_pos x,dif_pos y,Sum.inl.injEq] at root
    simp only [rootEndpointBin,dif_pos x,dif_pos y] at slot
    subst s;exact congrArg (fun v:Fin (w r) => (⟨r,v⟩:RootSlots w)) (Fin.ext slot)
  · simp [rootEndpointBin,x,y] at eq
  · simp [rootEndpointBin,x,y] at eq
  · have roots := congrArg (fun z:(R⊕RootSlots w)×Fin k => z.1) eq
    simpa only [rootEndpointBin,dif_neg x,dif_neg y,Sum.inr.injEq] using roots

variable [Finite R] [Finite C]
structure ActualAssignmentLayers {L:R→C→Prop} {w:R→ℕ} {k:ℕ}
    {M:(portIncidenceGraph (slotIncidence L w k)).Subgraph} (hm:M.IsMatching) (A:Set R) where
  colour : ↥(PortMatching.cores M)→Fin k
  coreUnique : ∀i j,colour i=colour j → i.val.1=j.val.1 → i=j
  baseUnique : ∀i j,colour i=colour j →
    (PortMatching.mates hm i).val.2.val<k → (PortMatching.mates hm j).val.2.val<k →
    (PortMatching.mates hm i).val.1=(PortMatching.mates hm j).val.1 → i=j
  required : ∀r∈A,∀v:Fin k,∃i,colour i=v ∧ (PortMatching.mates hm i).val.1=r ∧ (PortMatching.mates hm i).val.2.val<k

theorem layer_the_same_slot_matching {L:R→C→Prop} {w:R→ℕ} {k:ℕ} (live:0<k)
    (M:(portIncidenceGraph (slotIncidence L w k)).Subgraph) (hm:M.IsMatching) (A:Set R)
    (base:∀r∈A,k≤w r) (cover:requiredRootSlots A w k⊆PortMatching.roots M) :
    Nonempty (ActualAssignmentLayers hm A) := by
  let J := PortMatching.cores M
  let a := PortMatching.mates hm
  let l : ↥J↪C×Fin k := Function.Embedding.subtype (·∈J)
  let r := (a.toEmbedding.trans (Function.Embedding.subtype (·∈PortMatching.roots M))).trans
    (⟨rootEndpointBin w live,root_endpoint_bin_injective w live⟩:RootSlots w↪(R⊕RootSlots w)×Fin k)
  obtain ⟨col,safe⟩ := colour_partial_endpoint_slots k l r
  have safeR (i j:↥J) (same:col i=col j) (p:(a i).val.2.val<k) (q:(a j).val.2.val<k)
      (eq:(a i).val.1=(a j).val.1) : i=j := by
    apply safe i j same (Or.inr ?_)
    change (rootEndpointBin w live (a i).val).1=(rootEndpointBin w live (a j).val).1
    simp only [rootEndpointBin,dif_pos p,dif_pos q,eq]
  refine ⟨⟨col,fun i j same eq => safe i j same (Or.inl eq),safeR,?_⟩⟩
  intro x hx v
  let slot (b:Fin k) : RootSlots w := ⟨x,⟨b.val,b.isLt.trans_le (base x hx)⟩⟩
  have paid (b:Fin k) : slot b∈PortMatching.roots M := cover (show slot b∈requiredRootSlots A w k from ⟨hx,b.isLt⟩)
  let who (b:Fin k) : ↥J := a.symm ⟨slot b,paid b⟩
  have original (b:Fin k) : (a (who b)).val=slot b := congrArg Subtype.val (a.apply_symm_apply _)
  have low (b:Fin k) : (a (who b)).val.2.val<k := by rw [original];exact b.isLt
  have parent (b:Fin k) : (a (who b)).val.1=x := by rw [original]
  have inj : Function.Injective (fun b => col (who b)) := by
    intro b c same
    have eq := safeR _ _ same (low b) (low c) ((parent b).trans (parent c).symm)
    have tags := congrArg (fun i:↥J => (a i).val) eq
    change (a (who b)).val=(a (who c)).val at tags;rw [original,original] at tags
    exact Fin.ext (congrArg (fun t:RootSlots w => t.2.val) tags)
  obtain ⟨b,done⟩ := Finite.surjective_of_injective inj v
  exact ⟨who b,done,parent b,low b⟩

#print axioms root_endpoint_bin_injective
#print axioms layer_the_same_slot_matching
end JSP452Audit.StarHost
