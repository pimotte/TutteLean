import Mathlib.Combinatorics.SimpleGraph.Clique

import TutteLean.Defs

namespace SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

lemma isClique_even_iff_matches [DecidableEq V]
    (u : Set V) (hu : Set.Finite u) (hc : G.IsClique u) : Even u.ncard ↔ ∃ (M : Subgraph G), M.verts = u ∧ M.IsMatching := by
  haveI : Fintype u := hu.fintype
  refine ⟨?_ , by
    rintro ⟨M, ⟨hMl, hMr⟩⟩
    haveI : Fintype M.verts := hMl ▸ hu.fintype
    subst hMl
    simpa [Set.ncard_eq_toFinset_card _ hu, Set.toFinite_toFinset,
      Set.toFinset_card] using hMr.even_card
    ⟩
  intro he
  cases' Set.eq_empty_or_nonempty u with h h
  · subst h
    use ⊥
    simp only [Subgraph.verts_bot, true_and]
    intro _ h
    contradiction
  · obtain ⟨x, y, ⟨hx, hy, hxy⟩⟩ := (Set.one_lt_ncard_iff hu).mp (Set.one_lt_ncard_of_nonempty_of_even hu h he)
    let u' := u \ {x, y}
    have : insert x (insert y (u \ {x, y})) = u := by
      ext v
      simp only [Set.mem_insert_iff, Set.mem_diff, Set.mem_singleton_iff]
      rw [← or_assoc]
      by_cases h : v = x ∨ v = y
      · cases' h with h' h' <;> subst h' <;> simpa
      · simp only [h, not_false_eq_true, and_true, false_or]
    have hu'e : Even (u \ {x, y}).ncard := by
      rw [← Set.odd_card_insert_iff (hu.diff) (by simp : y ∉ u \ {x, y})]
      rw [← Set.even_card_insert_iff (insert y (u \ {x, y})).toFinite (by
        simp [hxy] : x ∉ (insert y (u \ {x, y})))]
      rwa [this]
    have hu'c := hc.subset (Set.diff_subset : u' ⊆ u)
    have hu'f := @hu.diff _  _ {x, y}
    obtain ⟨M, hM⟩ := (isClique_even_iff_matches u' hu'f hu'c).mp hu'e
    use M ⊔ subgraphOfAdj _ (hc hx hy hxy)
    simp only [Subgraph.verts_sup, hM.1, subgraphOfAdj_verts]
    refine ⟨by
      rw [Set.diff_union_self]
      exact Set.union_eq_self_of_subset_right (Set.pair_subset hx hy), ?_⟩
    refine Subgraph.IsMatching.sup hM.2 (Subgraph.IsMatching.subgraphOfAdj (hc hx hy hxy)) ?h.hd
    simp only [support_subgraphOfAdj, hM.2.support_eq_verts, hM.1]
    exact Set.disjoint_sdiff_left
termination_by u.ncard
decreasing_by
· simp_wf
  refine Set.ncard_lt_ncard ?_ hu
  exact ⟨Set.diff_subset, by
    rw [@Set.not_subset_iff_exists_mem_not_mem]
    use x
    exact ⟨hx, by simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, true_or,
      not_true_eq_false, and_false, not_false_eq_true]⟩⟩

lemma completeGraph_isClique (u : Set V) : (completeGraph V).IsClique u := by
  intro x _ y _ a_2 a_3
  simp_all only [Set.mem_univ, ne_eq, not_true_eq_false]

lemma completeGraph_even_iff_matches [Fintype V] [DecidableEq V] :
    Even (Fintype.card V) ↔ ∃ (M : Subgraph (completeGraph V)), M.verts = Set.univ ∧ M.IsMatching := by
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card, (set_fintype_card_eq_univ_iff _).mpr rfl] using
    isClique_even_iff_matches (Set.univ : Set V) Set.finite_univ (completeGraph_isClique _)

lemma existsIsMatching [Fintype V] [DecidableEq V]
  (u : Set V) (hu : Set.Finite u) (h : G.IsClique u) (uEven : Even (u.ncard)) : ((isClique_even_iff_matches u hu h).mp uEven).choose.IsMatching := by
  exact (Exists.choose_spec ((isClique_even_iff_matches u hu h).mp uEven)).2


lemma componentExistsRep (c : ConnectedComponent G) : ∃ v, SimpleGraph.connectedComponentMk G v = c := c.exists_rep

lemma oddSubOneEven (n : Nat) (h : Odd n) : Even (n - 1) := by
  obtain ⟨ k , hk ⟩ := h
  use k
  rw [hk]
  rw [Nat.add_sub_cancel]
  ring


lemma oddCliqueAlmostMatches [Fintype V] [DecidableEq V]
  {u : Set V} {v : V} (hv : v ∈ u) (h : G.IsClique u) (uOdd : Odd (u.ncard)) : ∃ (M : Subgraph G), insert v M.verts = u ∧ M.IsMatching := by
  haveI : Fintype u := Fintype.ofFinite _
  rw [@Set.ncard_eq_toFinset_card'] at uOdd
  rw [@Set.toFinset_card] at uOdd
  have u'Even : Even ((u \ {v} : Set V).ncard) := by
    rw [Set.ncard_eq_toFinset_card']
    rw [Set.toFinset_diff]
    simp only [Set.mem_setOf_eq, Set.toFinset_singleton]
    rw [Finset.sdiff_singleton_eq_erase]
    rw [Finset.card_erase_of_mem (Set.mem_toFinset.mpr hv)]
    rw [Set.toFinset_card]
    exact oddSubOneEven _ uOdd
  have u'Clique : G.IsClique (u \ {v}) := SimpleGraph.IsClique.subset (@Set.diff_subset V u {v}) h
  obtain ⟨ M , hM ⟩ := ((isClique_even_iff_matches (u \ {v}) (Set.toFinite (u \ {v})) u'Clique).mp u'Even)
  use M
  constructor
  · rw [hM.1]
    rw [Set.insert_diff_singleton]
    exact (Set.insert_eq_of_mem hv)
  · exact hM.2

lemma oddCliqueAlmostMatchesDoesNotContainNode [Fintype V] [DecidableEq V]
  {u : Set V} {v : V} (hv : v ∈ u) (h : G.IsClique u) (uOdd : Odd (u.ncard)) : v ∉ (oddCliqueAlmostMatches hv h uOdd).choose.verts := by
  haveI (s : Set V) : Fintype s := Fintype.ofFinite _
  have hM := (oddCliqueAlmostMatches hv h uOdd).choose_spec

  have : Even (Fintype.card (oddCliqueAlmostMatches hv h uOdd).choose.verts) := by
    rw [← @Set.toFinset_card]
    exact SimpleGraph.Subgraph.IsMatching.even_card hM.2
  intro hv
  rw [Set.insert_eq_of_mem hv] at hM

  rw [← hM.1] at uOdd
  rw [← Nat.not_odd_iff_even] at this
  -- rw? at this
  -- rw [← @Set.toFinset_card] at uOdd
  rw [Set.ncard_eq_toFinset_card] at uOdd
  rw [@Set.Finite.card_toFinset] at uOdd
  exact this uOdd


lemma oddCliqueAlmostMatchesSubset [Fintype V] [DecidableEq V]
  {u : Set V} {v : V} (hv : v ∈ u) (h : G.IsClique u) (uOdd : Odd (u.ncard)) : (oddCliqueAlmostMatches hv h uOdd).choose.verts ⊆ u := by
  intro x hx
  rw [← (oddCliqueAlmostMatches hv h uOdd).choose_spec.1]
  exact Set.subset_insert _ _ hx

lemma isNotClique_iff (G : SimpleGraph V) (u : Set V) : ¬G.IsClique u ↔ ∃ (v w : u), v ≠ w ∧ ¬ G.Adj v w := by
  constructor
  · rw [@isClique_iff_induce_eq]
    intro h
    by_contra! hc
    apply h
    ext v w
    rw [@top_adj]
    exact ⟨fun h' ↦ Adj.ne' (adj_symm (induce u G) h'), fun h' ↦ hc v w h' ⟩
  · rintro ⟨ v , ⟨ w , h ⟩ ⟩
    rw [SimpleGraph.isClique_iff]
    by_contra! hc
    exact h.2 (hc (Subtype.coe_prop v) (w.coe_prop) (Subtype.coe_ne_coe.mpr h.1))
