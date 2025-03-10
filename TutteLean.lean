import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Matching
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Operations
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card

import TutteLean.Defs
import TutteLean.Supp
import TutteLean.SingleEdge
import TutteLean.Clique
import TutteLean.PartNew
import TutteLean.Part2

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma reachable_induce_supp (c : ConnectedComponent G) (v w : V) (hv : v ∈ c.supp) (hw : w ∈ c.supp) (p : G.Walk v w) : (G.induce c.supp).Reachable ⟨v, hv⟩ ⟨w, hw⟩ := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    have : v ∈ c.supp := (c.mem_supp_congr_adj h).mp hv
    obtain ⟨q⟩ := ih this hw
    have hadj : (G.induce c.supp).Adj ⟨u, hv⟩ ⟨v, this⟩ := h
    use q.cons hadj

lemma ConnectedComponent.connected_induce_supp (c : ConnectedComponent G) : (G.induce c.supp).Connected := by
  rw [connected_iff_exists_forall_reachable]
  use ⟨c.out, c.out_eq⟩
  intro w
  have hwc := (c.mem_supp_iff w).mp (Subtype.coe_prop w)
  obtain ⟨p⟩ := ConnectedComponent.exact (show G.connectedComponentMk c.out = G.connectedComponentMk w from by
    rw [hwc]
    simp [connectedComponentMk])
  exact reachable_induce_supp c _ _ c.out_eq hwc p

-- In walk_lemmas
lemma walk_length_one_adj : (∃ (p : G.Walk u v), p.length = 1) ↔ G.Adj u v := by
  refine ⟨?_, fun h ↦ ⟨h.toWalk, by simp⟩⟩
  rintro ⟨p , hp⟩
  match p with
  | Walk.nil' u => simp only [Walk.length_nil, zero_ne_one] at hp
  | Walk.cons' u v w h p' =>
    simp only [Walk.length_cons, add_left_eq_self] at hp
    exact ((p'.eq_of_length_eq_zero hp) ▸ h)

-- In walk_lemmas
lemma verts_of_walk (p : G.Walk v w) (hp : p.length = G.dist v w) (hl : 1 < G.dist v w) : ∃ (x a b : V), G.Adj x a ∧ G.Adj a b ∧ ¬ G.Adj x b ∧ x ≠ b := by
  use v, p.getVert 1, p.getVert 2
  have hnp : ¬p.Nil := by simpa [SimpleGraph.Walk.nil_iff_length_eq, hp] using Nat.not_eq_zero_of_lt hl
  have hntp : ¬p.tail.Nil := by
    rw [Walk.not_nil_iff_lt_length]
    rw [← p.length_tail_add_one hnp] at hp
    omega
  have hadj1 : G.Adj v (p.getVert 1) := by simpa using p.adj_snd hnp
  have hadj2 : G.Adj (p.getVert 1) (p.getVert 2) := by simpa using p.adj_getVert_succ (hp ▸ hl)
  have : p.tail.tail.length < p.tail.length := by
    rw [← p.tail.length_tail_add_one hntp]
    omega
  have : p.tail.length < p.length := by
      rw [← p.length_tail_add_one hnp]
      omega
  by_cases hv : v = p.getVert 2
  · have : G.dist v w ≤ p.tail.tail.length := by
      simpa [hv, p.getVert_tail] using dist_le p.tail.tail
    omega
  by_cases hadj : G.Adj v (p.getVert 2)
  · have : G.dist v w ≤ p.tail.tail.length + 1 := by simpa using dist_le (p.tail.tail.cons (p.getVert_tail ▸ hadj))
    omega
  simp_all

-- In walk_lemmas
lemma dist_gt_one_of_ne_and_nadj (h : G.Reachable u v) (hne : u ≠ v) (hnadj : ¬G.Adj u v) : 1 < G.dist u v := by
  have : 1 ≠ G.dist u v := by
    by_contra! hc
    obtain ⟨p, hp⟩ := Reachable.exists_path_of_dist h
    rw [← hc] at hp
    exact hnadj (walk_length_one_adj.mp ⟨p, hp.2⟩)
  exact Nat.lt_of_le_of_ne (h.pos_dist_of_ne hne) this

theorem tutte_blocker_odd [Fintype V]
    (hodd : Odd (Fintype.card V)) : ∃ u, G.TutteBlocker u  := by
  use ∅
  have ⟨c, hc⟩ := Classical.inhabited_of_nonempty
    (Finite.card_pos_iff.mp <| Odd.pos <|
    (odd_card_iff_odd_components ((⊤ : Subgraph G).deleteVerts ∅).coe).mp (by
    simpa [Fintype.card_congr (Equiv.Set.univ V)] using hodd))
  rw [TutteBlocker, Set.ncard_empty, Set.ncard_pos]
  use c

lemma tutte_necessary [Fintype V]
  {M : Subgraph G} (hM : M.IsPerfectMatching) (u : Set V) :
    ¬ G.TutteBlocker u := by
  let f : {c : ConnectedComponent ((⊤ : Subgraph G).deleteVerts u).coe | Odd (Nat.card c.supp)} → u :=
      fun c => ⟨(c.1.odd_matches_node_outside hM c.2).choose,(c.1.odd_matches_node_outside hM c.2).choose_spec.1⟩
  simpa [TutteBlocker, Set.Nat.card_coe_set_eq] using Finite.card_le_of_injective f (by
    intro x y hxy
    obtain ⟨v, hv⟩:= (x.1.odd_matches_node_outside hM x.2).choose_spec.2
    obtain ⟨w, hw⟩:= (y.1.odd_matches_node_outside hM y.2).choose_spec.2
    obtain ⟨v', hv'⟩ := (M.isPerfectMatching_iff).mp hM (f y)
    rw [Subtype.mk_eq_mk.mp hxy, (Subtype.val_injective (hv'.2 _ hw.1.symm ▸ hv'.2 _ hv.1.symm) : v = w)] at hv
    exact Subtype.mk_eq_mk.mpr <| ConnectedComponent.eq_of_common_vertex hv.2 hw.2)

lemma tutte_sufficient [Fintype V] [DecidableEq V]
  (h : ∀ (M : G.Subgraph), ¬M.IsPerfectMatching) (hvEven : Even (Fintype.card V)) :
     ∃ u, G.TutteBlocker u := by
  classical
  obtain ⟨Gmax, hSubgraph, hMatchingFree, hMaximal⟩ := exists_maximal_isMatchingFree h
  suffices ∃ u, Set.ncard u <  {c : ((⊤ : Gmax.Subgraph).deleteVerts u).coe.ConnectedComponent | Odd (c.supp.ncard)}.ncard  by
    · obtain ⟨u, hu⟩ := this
      use u
      exact lt_of_lt_of_le hu (ncard_odd_components_mono _ (Subgraph.deleteVerts_mono' u hSubgraph))

  let Gsplit := Gmax.deleteUniversalVerts

  by_contra! hc
  have h' := hc Gmax.universalVerts
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_card] at h'
  have h'' := h'

  by_cases h' : ∀ (K : ConnectedComponent Gsplit.coe), Gsplit.coe.IsClique K.supp
  · rw [Fintype.card_eq_nat_card] at h''
    simp_rw [Fintype.card_eq_nat_card, Set.Nat.card_coe_set_eq] at h''
    obtain ⟨M, hM⟩ := tutte_part' hvEven h'' h'
    exact hMatchingFree M hM
  · push_neg at h'
    obtain ⟨K, hK⟩ := h'
    rw [isNotClique_iff] at hK
    obtain ⟨x, ⟨y, hxy⟩⟩ := hK
    obtain ⟨p , hp⟩ := SimpleGraph.Reachable.exists_path_of_dist (K.connected_induce_supp x y)
    obtain ⟨x, ⟨a, ⟨b, hxab⟩⟩⟩ := verts_of_walk p hp.2 (dist_gt_one_of_ne_and_nadj (Walk.reachable p) hxy.1 hxy.2)

    have ha : (a : V) ∉ Gmax.universalVerts := a.1.2.2
    have hc : ∃ (c : V), ¬ Gmax.Adj a c ∧ (a : V) ≠ c := by
      have : ¬ ∀ (w : V), (a : V) ≠ w → Gmax.Adj (w : V) a := by exact ha
      push_neg at this
      obtain ⟨c, hc⟩ := this
      exact ⟨c, ⟨fun h ↦ hc.2 h.symm, hc.1⟩⟩
    obtain ⟨c, hc⟩ := hc

    have hbnec : b.val.val ≠ c := by
      intro h
      apply (h ▸ hc.1)
      simp only [comap_adj, Function.Embedding.coe_subtype, Subgraph.coe_adj, ne_eq] at hxab
      simpa using hxab.2.1.adj_sub

    have hG1nxb : ¬ Gmax.Adj x.val.val b.val.val := by
      intro h
      apply hxab.2.2.1
      simp [h, Gsplit, deleteUniversalVerts]

    have hG1 := left_lt_sup.mpr (by rw [edge_le_iff (fun h ↦ hxab.2.2.2 (Subtype.val_injective (Subtype.val_injective h)))]; exact hG1nxb)
    have hG2 := left_lt_sup.mpr (by rw [edge_le_iff (fun h ↦ hc.2 h)]; exact hc.1)

    obtain ⟨M1, hM1⟩ := hMaximal _ hG1
    obtain ⟨M2, hM2⟩ := hMaximal _ hG2

    have hGMaxadjax : Gmax.Adj ↑↑a ↑↑x := by
      refine Gsplit.coe_adj_sub _ _ (adj_symm Gsplit.coe ?_)
      simpa using hxab.1

    have hGMaxadjab : Gmax.Adj ↑↑a ↑↑b := by
      refine Gsplit.coe_adj_sub _ _ (adj_symm Gsplit.coe ?_)
      simpa using hxab.2.1.symm

    have hcnex : c ≠ x.val.val := fun hxc ↦ hc.1 (hxc ▸ hGMaxadjax)

    obtain ⟨Mcon, hMcon⟩ := tutte_part2 hGMaxadjax.symm hGMaxadjab hG1nxb hc.1 (by
      intro h
      apply hxab.2.2.2
      exact Subtype.val_injective (Subtype.val_injective h)) hcnex.symm hc.2 hbnec (hMaximal _ hG1) (hMaximal _ hG2)
    exact hMatchingFree Mcon hMcon


theorem tutte [Fintype V] :
    (∃ (M : Subgraph G) , M.IsPerfectMatching) ↔
      (∀ (u : Set V), ¬ G.TutteBlocker u) := by
  classical
  refine ⟨by rintro ⟨M, hM⟩; apply tutte_necessary hM, ?_⟩
  contrapose!
  intro h
  by_cases hvOdd : Odd (Fintype.card V)
  · exact tutte_blocker_odd hvOdd
  · exact tutte_sufficient h (Nat.not_odd_iff_even.mp hvOdd)
