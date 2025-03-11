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

lemma TutteBlocker_mono [Finite V] {u : Set V} (h : G ≤ G') (ht : G'.TutteBlocker u) : G.TutteBlocker u := by
  simp only [TutteBlocker, Subgraph.induce_verts, Subgraph.verts_top] at *
  have := ncard_odd_components_mono _ (Subgraph.deleteVerts_mono' (G := G) (G' := G') u h)
  omega

lemma tutte_sufficient [Fintype V] [DecidableEq V]
  (h : ∀ (M : G.Subgraph), ¬M.IsPerfectMatching) (hvEven : Even (Fintype.card V)) :
     ∃ u, G.TutteBlocker u := by
  classical
  obtain ⟨Gmax, hSubgraph, hMatchingFree, hMaximal⟩ := exists_maximal_isMatchingFree h
  use Gmax.universalVerts
  apply TutteBlocker_mono hSubgraph
  by_contra! hc
  simp only [TutteBlocker, Set.ncard_eq_toFinset_card', Set.toFinset_card] at hc
  by_cases h' : ∀ (K : ConnectedComponent Gmax.deleteUniversalVerts.coe), Gmax.deleteUniversalVerts.coe.IsClique K.supp
  · rw [Fintype.card_eq_nat_card] at hc
    simp_rw [Fintype.card_eq_nat_card, Set.Nat.card_coe_set_eq] at hc
    push_neg at hc
    obtain ⟨M, hM⟩ := tutte_part' hvEven hc h'
    exact hMatchingFree M hM
  · push_neg at h'
    obtain ⟨K, hK⟩ := h'
    obtain ⟨x, ⟨y, hxy⟩⟩ := (isNotClique_iff _ _).mp hK
    obtain ⟨p , hp⟩ := SimpleGraph.Reachable.exists_path_of_dist (K.connected_induce_supp x y)
    obtain ⟨x, ⟨a, ⟨b, ⟨hxa, hxb, hnadjxb, hnxb⟩⟩⟩⟩ := verts_of_walk p hp.2 (dist_gt_one_of_ne_and_nadj (Walk.reachable p) hxy.1 hxy.2)
    simp only [deleteUniversalVerts, universalVerts, ne_eq, Subgraph.induce_verts,
      Subgraph.verts_top, comap_adj, Function.Embedding.coe_subtype, Subgraph.coe_adj,
      Subgraph.induce_adj, Subtype.coe_prop, Subgraph.top_adj, true_and] at hxa hxb hnadjxb
    obtain ⟨c, hc⟩ : ∃ (c : V), (a : V) ≠ c ∧ ¬ Gmax.Adj c a := by simpa [universalVerts] using a.1.2.2
    have hbnec : b.val.val ≠ c := fun h ↦ hc.2 (h ▸ hxb.symm)
    obtain ⟨_, hG1⟩ := hMaximal _ <| left_lt_sup.mpr (by rw [edge_le_iff (fun h ↦ hnxb (Subtype.val_injective (Subtype.val_injective h)))]; exact hnadjxb)
    obtain ⟨_, hG2⟩ := hMaximal _ <| left_lt_sup.mpr (by rw [edge_le_iff (fun h ↦ hc.1 h), adj_comm]; exact hc.2)
    have hcnex : c ≠ x.val.val := fun hxc ↦ hc.2 (hxc ▸ hxa)
    obtain ⟨Mcon, hMcon⟩ := tutte_part2 hxa hxb hnadjxb (fun hadj ↦ hc.2 hadj.symm) (by aesop)
      hcnex.symm hc.1 hbnec hG1 hG2
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
