module

public import Mathlib

/-!
# Erdős Problem 110: proof of the de Bruijn–Erdős variant

Proof of the statement of `Challenge.lean`.

Let `G` have infinite chromatic number and `n = k + 1`. By the de Bruijn–Erdős compactness
theorem (Mathlib's `SimpleGraph.nonempty_hom_of_forall_finite_subgraph_hom` with target the
complete graph on `k` colours), some finite subgraph is not `k`-colourable. Take one with the
fewest vertices. It has a vertex `v`; deleting `v` leaves a smaller finite subgraph, which is
`k`-colourable by minimality, and giving `v` a new colour shows the subgraph is
`(k + 1)`-colourable. So its chromatic number is exactly `k + 1`.
-/

@[expose] public section

open Filter

namespace Erdos110Proof

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- The de Bruijn–Erdős compactness theorem: if every finite subgraph of `G` is `k`-colourable,
then so is `G`. -/
lemma colorable_of_forall_finite (k : ℕ)
    (h : ∀ H : G.Subgraph, H.verts.Finite → H.coe.Colorable k) : G.Colorable k :=
  nonempty_hom_of_forall_finite_subgraph_hom fun H hH ↦ (h H hH).some

/-- Deleting one vertex lowers the number of colours needed by at most one. -/
lemma colorable_succ_of_deleteVerts (H : G.Subgraph) (v : V) (k : ℕ)
    (h : (H.deleteVerts {v}).coe.Colorable k) : H.coe.Colorable (k + 1) := by
  classical
  obtain ⟨c⟩ := h
  have hmem : ∀ w : H.verts, (w : V) ≠ v → (w : V) ∈ (H.deleteVerts {v}).verts := fun w hw ↦ by
    rw [Subgraph.deleteVerts_verts]
    exact ⟨w.2, hw⟩
  refine ⟨Coloring.mk (fun w ↦ if hw : (w : V) = v then Fin.last k
    else Fin.castSucc (c ⟨w, hmem w hw⟩)) ?_⟩
  intro a b hab
  have hne : (a : V) ≠ b := fun h ↦ hab.ne (Subtype.ext h)
  by_cases ha : (a : V) = v <;> by_cases hb : (b : V) = v
  · exact absurd (ha.trans hb.symm) hne
  · rw [dite_eq_left ha, dite_eq_right hb]
    exact (Fin.castSucc_lt_last _).ne'
  · rw [dite_eq_right ha, dite_eq_left hb]
    exact (Fin.castSucc_lt_last _).ne
  · rw [dite_eq_right ha, dite_eq_right hb, ne_eq, Fin.castSucc_inj]
    apply c.valid
    rw [Subgraph.coe_adj, Subgraph.deleteVerts_adj]
    exact ⟨a.2, ha, b.2, hb, hab⟩

theorem de_bruijn_erdos {V : Type*} (G : SimpleGraph V)
    (hG : G.chromaticNumber = ⊤) (n : ℕ) (hn : 1 ≤ n) :
    ∃ H : G.Subgraph, H.verts.Finite ∧ H.coe.chromaticNumber = (n : ℕ∞) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  -- Some finite subgraph is not `k`-colourable.
  have hex : ∃ j, ∃ H : G.Subgraph, H.verts.Finite ∧ ¬ H.coe.Colorable k ∧ H.verts.ncard = j := by
    by_contra! hall
    have hk : G.Colorable k :=
      colorable_of_forall_finite k fun H hH ↦ by
        by_contra hc
        exact hall _ H hH hc rfl
    have := hk.chromaticNumber_le
    rw [hG] at this
    exact absurd this (by simp)
  -- Take one with the fewest vertices.
  classical
  obtain ⟨H, hfin, hnot, hcard⟩ := Nat.find_spec hex
  refine ⟨H, hfin, ?_⟩
  rw [Nat.cast_add, Nat.cast_one, chromaticNumber_eq_iff_colorable_not_colorable]
  refine ⟨?_, hnot⟩
  -- `H` has a vertex, since a graph without vertices is `k`-colourable.
  obtain ⟨v, hv⟩ : H.verts.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have : IsEmpty H.verts := Set.isEmpty_coe_sort.2 hemp
    exact hnot (Colorable.of_isEmpty k)
  apply colorable_succ_of_deleteVerts H v k
  by_contra hc
  have hlt : (H.deleteVerts {v}).verts.ncard < Nat.find hex := by
    rw [Subgraph.deleteVerts_verts, ← hcard]
    exact Set.ncard_sdiff_singleton_lt_of_mem hv hfin
  exact Nat.find_min hex hlt ⟨H.deleteVerts {v},
    by rw [Subgraph.deleteVerts_verts]; exact hfin.subset Set.sdiff_subset, hc, rfl⟩

end Erdos110Proof

namespace Erdos110

theorem erdos_110.variants.de_bruijn_erdos {V : Type*} (G : SimpleGraph V)
    (hG : G.chromaticNumber = ⊤) (n : ℕ) (hn : 1 ≤ n) :
    ∃ H : G.Subgraph, H.verts.Finite ∧ H.coe.chromaticNumber = (n : ℕ∞) :=
  Erdos110Proof.de_bruijn_erdos G hG n hn

end Erdos110
