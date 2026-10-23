/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import FormalConjecturesUtil

/-!
# Written on the Wall II - Conjecture 19

*Reference:*
[E. DeLaVina, Written on the Wall II, Conjectures of Graffiti.pc](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)
-/

@[expose] public section

namespace WrittenOnTheWallII.GraphConjecture19

open SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [Fintype α] [DecidableEq α] in
/-- An induced subgraph on `s : Finset α` is bipartite whenever `s` admits a proper 2-coloring. -/
@[category API, AMS 5]
lemma induce_isBipartite_of_coloring (G : SimpleGraph α) (s : Finset α)
    (c : α → Fin 2) (hc : ∀ u ∈ s, ∀ v ∈ s, G.Adj u v → c u ≠ c v) :
    (G.induce (s : Set α)).IsBipartite :=
  ⟨Coloring.mk (fun v => c v.1) fun {u v} huv => hc u.1 u.2 v.1 v.2 huv⟩

omit [Fintype α] [DecidableEq α] in
/-- Every walk `p` of length `L` can be split at any distance `d ≤ L` into a prefix walk of length `d`
and a suffix walk of length `L - d`. -/
@[category API, AMS 5]
lemma exists_length_eq_and_length_eq_sub {G : SimpleGraph α}
    {u x : α} (p : G.Walk u x) {d : ℕ} (hd : d ≤ p.length) :
    ∃ (z : α) (p₁ : G.Walk u z) (p₂ : G.Walk z x),
      p₁.length = d ∧ p₂.length = p.length - d := by
  induction d generalizing u with
  | zero =>
    exact ⟨u, .nil, p, rfl, Nat.sub_zero _⟩
  | succ d ih =>
    cases p with
    | nil => simp at hd
    | @cons _ v _ huv q =>
      simp only [Walk.length_cons, Nat.add_le_add_iff_right] at hd
      obtain ⟨z, q₁, p₂, hq₁, hp₂⟩ := ih q hd
      exact ⟨z, .cons huv q₁, p₂, by simp [hq₁], by simp [hp₂, Nat.succ_sub_succ]⟩

omit [Fintype α] [DecidableEq α] in
/-- Geodesic interpolation: in a connected graph `G`, for any `u, x : α` and `d ≤ G.dist u x`,
there exists a vertex `z` at distance `d` from `u` and distance `G.dist u x - d` from `x`. -/
@[category API, AMS 5]
lemma exists_dist_eq_and_dist_eq_sub {G : SimpleGraph α}
    (hconn : G.Connected) (u x : α) {d : ℕ} (hd : d ≤ G.dist u x) :
    ∃ z : α, G.dist u z = d ∧ G.dist z x = G.dist u x - d := by
  obtain ⟨p, hp⟩ := (hconn u x).exists_walk_length_eq_dist
  obtain ⟨z, p₁, p₂, hp₁, hp₂⟩ := exists_length_eq_and_length_eq_sub p (hp.symm ▸ hd)
  have h1 : G.dist u z ≤ d := hp₁ ▸ G.dist_le p₁
  have h2 : G.dist z x ≤ G.dist u x - d := by
    calc G.dist z x ≤ p₂.length := G.dist_le p₂
      _ = G.dist u x - d := by rw [hp₂, hp]
  have h3 : G.dist u x ≤ G.dist u z + G.dist z x := hconn.dist_triangle
  exact ⟨z, by omega, by omega⟩

omit [Fintype α] in
/-- If `B d` lies in the distance sphere `{v | G.dist u v = d}` for each `d ∈ s`, then the sets
`B d` are pairwise disjoint and the cardinality of `s.biUnion B` is `∑ d ∈ s, (B d).card`. -/
@[category API, AMS 5]
lemma card_biUnion_eq_sum_of_dist
    (G : SimpleGraph α) (u : α) (s : Finset ℕ) (B : ℕ → Finset α)
    (hdist : ∀ d ∈ s, ∀ v ∈ B d, G.dist u v = d) :
    (s.biUnion B).card = ∑ d ∈ s, (B d).card := by
  apply Finset.card_biUnion
  intro d₁ hd₁ d₂ hd₂ hne
  simp only [Function.onFun, Finset.disjoint_left]
  intro v hv₁ hv₂
  exact hne ((hdist d₁ hd₁ v hv₁).symm.trans (hdist d₂ hd₂ v hv₂))

omit [Fintype α] in
/-- Sphere-Parity Bipartite Construction: if each `B d` (`d ∈ s`) lies in the distance sphere
`{v | G.dist u v = d}` and is an independent set in `G`, then `G.induce (s.biUnion B)` is bipartite. -/
@[category API, AMS 5]
lemma induce_biUnion_isBipartite_of_dist
    {G : SimpleGraph α} (hconn : G.Connected) (u : α) (s : Finset ℕ) (B : ℕ → Finset α)
    (hdist : ∀ d ∈ s, ∀ v ∈ B d, G.dist u v = d)
    (hindep : ∀ d ∈ s, ∀ x ∈ B d, ∀ y ∈ B d, ¬G.Adj x y) :
    (G.induce ((s.biUnion B : Finset α) : Set α)).IsBipartite := by
  refine induce_isBipartite_of_coloring G (s.biUnion B)
    (fun v => ⟨G.dist u v % 2, Nat.mod_lt _ (by omega)⟩) ?_
  intro x hx y hy hxy hcol
  rw [Finset.mem_biUnion] at hx hy
  obtain ⟨d₁, hd₁, hx₁⟩ := hx
  obtain ⟨d₂, hd₂, hy₂⟩ := hy
  have hdx : G.dist u x = d₁ := hdist d₁ hd₁ x hx₁
  have hdy : G.dist u y = d₂ := hdist d₂ hd₂ y hy₂
  have hle1 : G.dist u x ≤ G.dist u y + G.dist y x := hconn.dist_triangle
  have hle2 : G.dist u y ≤ G.dist u x + G.dist x y := hconn.dist_triangle
  have hadj1 : G.dist x y ≤ 1 := G.dist_le (.cons hxy .nil)
  have hadj2 : G.dist y x ≤ 1 := G.dist_le (.cons hxy.symm .nil)
  have hmod : G.dist u x % 2 = G.dist u y % 2 := congrArg Fin.val hcol
  have hd_eq : d₁ = d₂ := by omega
  subst hd_eq
  exact hindep d₁ hd₁ x hx₁ y hy₂ hxy

omit [DecidableEq α] in
/-- In a connected finite graph `G`, every vertex `u` has a vertex `w` at distance `(G.eccent u).toNat`. -/
@[category API, AMS 5]
lemma exists_dist_eq_eccent_toNat
    {G : SimpleGraph α} (hconn : G.Connected) (u : α) :
    ∃ w : α, G.dist u w = (G.eccent u).toNat := by
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite u
  refine ⟨w, ?_⟩
  rw [← hw, ← (hconn.preconnected u w).coe_dist_eq_edist, ENat.toNat_natCast]

omit [DecidableEq α] in
/-- In a connected finite graph `G`, `(G.eccent u).toNat ≤ G.diam` for every vertex `u`. -/
@[category API, AMS 5]
lemma eccent_toNat_le_diam
    {G : SimpleGraph α} (hconn : G.Connected) (u : α) :
    (G.eccent u).toNat ≤ G.diam := by
  have : Nonempty α := ⟨u⟩
  exact ENat.toNat_le_toNat G.eccent_le_ediam (G.connected_iff_ediam_ne_top.mp hconn)

/-- Every finite graph contains an independent `Finset` of cardinality `G.indepNum`. -/
@[category API, AMS 5]
lemma exists_isIndepSet_card_eq_indepNum {β : Type*} [Fintype β] (H : SimpleGraph β) :
    ∃ s : Finset β, H.IsIndepSet (s : Set β) ∧ s.card = H.indepNum := by
  unfold SimpleGraph.indepNum
  have hne : {n : ℕ | ∃ s : Finset β, H.IsNIndepSet n s}.Nonempty :=
    ⟨0, ∅, ⟨by simp [SimpleGraph.IsIndepSet], rfl⟩⟩
  have hbdd : BddAbove {n : ℕ | ∃ s : Finset β, H.IsNIndepSet n s} :=
    ⟨Fintype.card β, fun n ⟨t, ht⟩ => ht.card_eq ▸ t.card_le_univ⟩
  obtain ⟨s, hs⟩ := Nat.sSup_mem hne hbdd
  exact ⟨s, hs.isIndepSet, hs.card_eq⟩

omit [DecidableEq α] in
/-- For any vertex `u` in a connected graph `G`, there exists a `Finset α` of cardinality
`indepNeighborsCard G u` contained in the unit sphere `{v | G.dist u v = 1}` that is an
independent set in `G`. -/
@[category API, AMS 5]
lemma exists_indepSet_neighborSet_card_eq (G : SimpleGraph α) (u : α) :
    ∃ I : Finset α, I.card = indepNeighborsCard G u ∧
      (∀ v ∈ I, G.dist u v = 1) ∧ (∀ x ∈ I, ∀ y ∈ I, ¬G.Adj x y) := by
  classical
  obtain ⟨s, hs_ind, hs_card⟩ := exists_isIndepSet_card_eq_indepNum (G.induce (G.neighborSet u))
  let I : Finset α := s.map ⟨Subtype.val, Subtype.val_injective⟩
  refine ⟨I, ?_, ?_, ?_⟩
  · rw [Finset.card_map, hs_card, indepNeighborsCard]
  · intro v hv
    rcases Finset.mem_map.mp hv with ⟨a, _, rfl⟩
    exact G.dist_eq_one_iff_adj.mpr a.2
  · intro x hx y hy hxy
    rcases Finset.mem_map.mp hx with ⟨a, ha, rfl⟩
    rcases Finset.mem_map.mp hy with ⟨b, hb, rfl⟩
    have hne : a ≠ b := fun h => G.ne_of_adj hxy (congrArg Subtype.val h)
    exact hs_ind ha hb hne hxy

/-- If each `B d` (`d ∈ s`) lies in the distance sphere `{v | G.dist u v = d}` and is an
independent set in `G`, then `∑ d ∈ s, (B d).card ≤ G.largestInducedBipartiteSubgraphSize`. -/
@[category API, AMS 5]
lemma card_biUnion_le_largestInducedBipartiteSubgraphSize (G : SimpleGraph α) (hconn : G.Connected)
    (u : α) (s : Finset ℕ) (B : ℕ → Finset α)
    (hdist : ∀ d ∈ s, ∀ v ∈ B d, G.dist u v = d)
    (hindep : ∀ d ∈ s, ∀ x ∈ B d, ∀ y ∈ B d, ¬G.Adj x y) :
    ∑ d ∈ s, (B d).card ≤ G.largestInducedBipartiteSubgraphSize := by
  rw [← card_biUnion_eq_sum_of_dist G u s B hdist]
  unfold largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card α, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨s.biUnion B, induce_biUnion_isBipartite_of_dist hconn u s B hdist hindep, rfl⟩

omit [DecidableEq α] in
/-- On a nontrivial finite vertex type, `indepNeighborsCard G` attains its maximum at some vertex `u`,
and `sSup (Set.range (indepNeighbors G)) = (indepNeighborsCard G u : ℝ)`. -/
@[category API, AMS 5]
lemma exists_max_indepNeighborsCard_and_csSup_eq (G : SimpleGraph α) [Nontrivial α] :
    ∃ u : α, (∀ v : α, indepNeighborsCard G v ≤ indepNeighborsCard G u) ∧
      sSup (Set.range (indepNeighbors G)) = (indepNeighborsCard G u : ℝ) := by
  obtain ⟨u, _, hu⟩ := Finset.exists_max_image Finset.univ (indepNeighborsCard G) Finset.univ_nonempty
  refine ⟨u, fun v => hu v (Finset.mem_univ v), ?_⟩
  apply le_antisymm
  · apply csSup_le (Set.range_nonempty (indepNeighbors G))
    rintro _ ⟨v, rfl⟩
    simp only [indepNeighbors]
    exact_mod_cast hu v (Finset.mem_univ v)
  · apply le_csSup
    · refine ⟨(indepNeighborsCard G u : ℝ), ?_⟩
      rintro _ ⟨v, rfl⟩
      simp only [indepNeighbors]
      exact_mod_cast hu v (Finset.mem_univ v)
    · exact ⟨u, rfl⟩

/-- Case 1 lower bound: for any vertex `u` in a nontrivial connected graph `G`,
`(G.eccent u).toNat + indepNeighborsCard G u ≤ G.largestInducedBipartiteSubgraphSize`. -/
@[category API, AMS 5]
lemma eccent_toNat_add_indepNeighborsCard_le_bipartite (G : SimpleGraph α) [Nontrivial α]
    (hconn : G.Connected) (u : α) :
    (G.eccent u).toNat + indepNeighborsCard G u ≤ G.largestInducedBipartiteSubgraphSize := by
  obtain ⟨I, hI_card, hI_dist, hI_ind⟩ := exists_indepSet_neighborSet_card_eq G u
  obtain ⟨w, hw⟩ := exists_dist_eq_eccent_toNat hconn u
  set e := (G.eccent u).toNat
  have he_pos : 1 ≤ e := by
    obtain ⟨v, hv⟩ := exists_ne u
    have hpos : 0 < G.dist u v := (hconn u v).pos_dist_of_ne hv.symm
    have hle : G.dist u v ≤ e := by
      have hed : G.edist u v ≤ G.eccent u := G.edist_le_eccent
      have hne_top : G.eccent u ≠ ⊤ :=
        ne_top_of_le_ne_top (G.connected_iff_ediam_ne_top.mp hconn) G.eccent_le_ediam
      have hcast := ENat.toNat_le_toNat hed hne_top
      rwa [← (hconn.preconnected u v).coe_dist_eq_edist, ENat.toNat_natCast] at hcast
    omega
  let B : ℕ → Finset α := fun d =>
    if d = 0 then {u}
    else if d = 1 then I
    else if hd : d ≤ e then
      {Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u w (hw ▸ hd))}
    else ∅
  have hdist : ∀ d ∈ Finset.range (e + 1), ∀ v ∈ B d, G.dist u v = d := by
    intro d hd v hv
    rw [Finset.mem_range] at hd
    dsimp [B] at hv
    split_ifs at hv with hd0 hd1 hde
    · simp only [Finset.mem_singleton] at hv
      subst hv hd0
      exact G.dist_self
    · subst hd1
      exact hI_dist v hv
    · simp only [Finset.mem_singleton] at hv
      subst hv
      exact (Classical.choose_spec (exists_dist_eq_and_dist_eq_sub hconn u w (hw ▸ hde))).1
    · omega
  have hindep : ∀ d ∈ Finset.range (e + 1), ∀ x ∈ B d, ∀ y ∈ B d, ¬G.Adj x y := by
    intro d _ x hx y hy hxy
    dsimp [B] at hx hy
    split_ifs at hx hy with hd0 hd1 hde
    · simp only [Finset.mem_singleton] at hx hy
      subst hx hy
      exact G.ne_of_adj hxy rfl
    · exact hI_ind x hx y hy hxy
    · simp only [Finset.mem_singleton] at hx hy
      subst hx hy
      exact G.ne_of_adj hxy rfl
    · simp at hx
  have hle := card_biUnion_le_largestInducedBipartiteSubgraphSize G hconn u (Finset.range (e + 1)) B hdist hindep
  have hsum : ∑ d ∈ Finset.range (e + 1), (B d).card = e + indepNeighborsCard G u := by
    rw [show e + 1 = (e - 1) + 1 + 1 by omega, Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : (B 0).card = 1 := by simp [B]
    have h1 : (B (0 + 1)).card = indepNeighborsCard G u := by simp [B, hI_card]
    have hrest : ∑ k ∈ Finset.range (e - 1), (B (k + 1 + 1)).card = e - 1 := by
      have hcongr : ∀ k ∈ Finset.range (e - 1), (B (k + 1 + 1)).card = 1 := by
        intro k hk
        rw [Finset.mem_range] at hk
        have hk2 : k + 1 + 1 ≤ e := by omega
        have hne0 : k + 1 + 1 ≠ 0 := by omega
        have hne1 : k + 1 + 1 ≠ 1 := by omega
        dsimp only [B]
        rw [if_neg hne0, if_neg hne1, dif_pos hk2, Finset.card_singleton]
      rw [Finset.sum_congr rfl hcongr, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    omega
  omega

/-- Auxiliary two-geodesic sphere construction when `G.dist x y = G.diam` and
`G.dist u y ≤ G.dist u x` and `(G.eccent u).toNat < G.diam`. -/
@[category API, AMS 5]
lemma diam_sub_one_add_indepNeighborsCard_le_bipartite_aux (G : SimpleGraph α) [Nontrivial α]
    (hconn : G.Connected) (u x y : α) (hxy : G.dist x y = G.diam)
    (hba : G.dist u y ≤ G.dist u x) (helt : (G.eccent u).toNat < G.diam) :
    G.diam - 1 + indepNeighborsCard G u ≤ G.largestInducedBipartiteSubgraphSize := by
  obtain ⟨I, hI_card, hI_dist, hI_ind⟩ := exists_indepSet_neighborSet_card_eq G u
  obtain ⟨w, hw⟩ := exists_dist_eq_eccent_toNat hconn u
  set e := (G.eccent u).toNat
  set D := G.diam
  set a := G.dist u x
  set b := G.dist u y
  have ha_le_e : a ≤ e := by
    have hed : G.edist u x ≤ G.eccent u := G.edist_le_eccent
    have hne_top : G.eccent u ≠ ⊤ :=
      ne_top_of_le_ne_top (G.connected_iff_ediam_ne_top.mp hconn) G.eccent_le_ediam
    have hcast := ENat.toNat_le_toNat hed hne_top
    rwa [← (hconn.preconnected u x).coe_dist_eq_edist, ENat.toNat_natCast] at hcast
  have hb_le_e : b ≤ e := le_trans hba ha_le_e
  have hD_le_ab : D ≤ a + b := by
    have htri : G.dist x y ≤ G.dist x u + G.dist u y := hconn.dist_triangle
    have hcomm : G.dist x u = a := G.dist_comm
    omega
  have he_pos : 1 ≤ e := by omega
  set dmin := max 2 ((a + b - D + 3) / 2)
  let B : ℕ → Finset α := fun d =>
    if d = 0 then {u}
    else if d = 1 then I
    else if hdb : dmin ≤ d ∧ d ≤ b then
      {Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u x (le_trans hdb.2 hba)),
       Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u y hdb.2)}
    else if hde : d ≤ e then
      {Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u w (hw ▸ hde))}
    else ∅
  have hpair_dist : ∀ d (hdb : dmin ≤ d ∧ d ≤ b),
      let x_d := Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u x (le_trans hdb.2 hba))
      let y_d := Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u y hdb.2)
      G.dist u x_d = d ∧ G.dist u y_d = d ∧ 2 ≤ G.dist x_d y_d := by
    intro d hdb
    set x_d := Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u x (le_trans hdb.2 hba))
    set y_d := Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u y hdb.2)
    have hspec_x : G.dist u x_d = d ∧ G.dist x_d x = a - d :=
      Classical.choose_spec (exists_dist_eq_and_dist_eq_sub hconn u x (le_trans hdb.2 hba))
    have hspec_y : G.dist u y_d = d ∧ G.dist y_d y = b - d :=
      Classical.choose_spec (exists_dist_eq_and_dist_eq_sub hconn u y hdb.2)
    have htri1 : G.dist x y ≤ G.dist x x_d + G.dist x_d y := hconn.dist_triangle
    have htri2 : G.dist x_d y ≤ G.dist x_d y_d + G.dist y_d y := hconn.dist_triangle
    have hcomm : G.dist x x_d = G.dist x_d x := G.dist_comm
    refine ⟨hspec_x.1, hspec_y.1, ?_⟩
    omega
  have hdist : ∀ d ∈ Finset.range (e + 1), ∀ v ∈ B d, G.dist u v = d := by
    intro d hd v hv
    rw [Finset.mem_range] at hd
    dsimp [B] at hv
    split_ifs at hv with hd0 hd1 hdb hde
    · simp only [Finset.mem_singleton] at hv
      subst hv hd0
      exact G.dist_self
    · subst hd1
      exact hI_dist v hv
    · obtain ⟨hux, huy, _⟩ := hpair_dist d hdb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl
      · exact hux
      · exact huy
    · simp only [Finset.mem_singleton] at hv
      subst hv
      exact (Classical.choose_spec (exists_dist_eq_and_dist_eq_sub hconn u w (hw ▸ hde))).1
    · omega
  have hindep : ∀ d ∈ Finset.range (e + 1), ∀ z₁ ∈ B d, ∀ z₂ ∈ B d, ¬G.Adj z₁ z₂ := by
    intro d _ z₁ hz₁ z₂ hz₂ hadj
    dsimp [B] at hz₁ hz₂
    split_ifs at hz₁ hz₂ with hd0 hd1 hdb hde
    · simp only [Finset.mem_singleton] at hz₁ hz₂
      subst hz₁ hz₂
      exact G.ne_of_adj hadj rfl
    · exact hI_ind z₁ hz₁ z₂ hz₂ hadj
    · obtain ⟨_, _, hdist2⟩ := hpair_dist d hdb
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz₁ hz₂
      rcases hz₁ with rfl | rfl <;> rcases hz₂ with rfl | rfl
      · exact G.ne_of_adj hadj rfl
      · have hle1 : G.dist _ _ ≤ 1 := G.dist_le (.cons hadj .nil)
        omega
      · have hle1 : G.dist _ _ ≤ 1 := G.dist_le (.cons hadj.symm .nil)
        omega
      · exact G.ne_of_adj hadj rfl
    · simp only [Finset.mem_singleton] at hz₁ hz₂
      subst hz₁ hz₂
      exact G.ne_of_adj hadj rfl
    · simp at hz₁
  have hle := card_biUnion_le_largestInducedBipartiteSubgraphSize G hconn u (Finset.range (e + 1)) B hdist hindep
  have hsum : G.diam - 1 + indepNeighborsCard G u ≤ ∑ d ∈ Finset.range (e + 1), (B d).card := by
    rw [show e + 1 = (e - 1) + 1 + 1 by omega, Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : (B 0).card = 1 := by simp [B]
    have h1 : (B (0 + 1)).card = indepNeighborsCard G u := by simp [B, hI_card]
    have hcard_k : ∀ k ∈ Finset.range (e - 1),
        (B (k + 1 + 1)).card = 1 + (if k ∈ Finset.Ico (dmin - 2) (b - 1) then 1 else 0) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have hk_le : k + 1 + 1 ≤ e := by omega
      have hne0 : k + 1 + 1 ≠ 0 := by omega
      have hne1 : k + 1 + 1 ≠ 1 := by omega
      by_cases hdb : dmin ≤ k + 1 + 1 ∧ k + 1 + 1 ≤ b
      · have hmem : k ∈ Finset.Ico (dmin - 2) (b - 1) := by
          rw [Finset.mem_Ico]
          omega
        obtain ⟨_, _, hdist2⟩ := hpair_dist (k + 1 + 1) hdb
        have hne_xy : Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u x (le_trans hdb.2 hba)) ≠
            Classical.choose (exists_dist_eq_and_dist_eq_sub hconn u y hdb.2) := by
          intro heq
          rw [heq, G.dist_self] at hdist2
          omega
        dsimp only [B]
        rw [if_neg hne0, if_neg hne1, dif_pos hdb, if_pos hmem, Finset.card_pair hne_xy]
      · have hnmem : k ∉ Finset.Ico (dmin - 2) (b - 1) := by
          rw [Finset.mem_Ico]
          omega
        dsimp only [B]
        rw [if_neg hne0, if_neg hne1, dif_neg hdb, dif_pos hk_le, if_neg hnmem,
          Finset.card_singleton, add_zero]
    have hrest : ∑ k ∈ Finset.range (e - 1), (B (k + 1 + 1)).card =
        (e - 1) + ((b - 1) - (dmin - 2)) := by
      rw [Finset.sum_congr rfl hcard_k, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        smul_eq_mul, mul_one, Finset.sum_boole, Nat.cast_id]
      have hfilter : (Finset.range (e - 1)).filter (fun x => x ∈ Finset.Ico (dmin - 2) (b - 1)) =
          Finset.Ico (dmin - 2) (b - 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [hfilter, Nat.card_Ico]
    omega
  exact le_trans hsum hle

/-- Case 2 lower bound: when `(G.eccent u).toNat < G.diam`, we have
`G.diam - 1 + indepNeighborsCard G u ≤ G.largestInducedBipartiteSubgraphSize`. -/
@[category API, AMS 5]
lemma diam_sub_one_add_indepNeighborsCard_le_bipartite (G : SimpleGraph α) [Nontrivial α]
    (hconn : G.Connected) (u : α) (helt : (G.eccent u).toNat < G.diam) :
    G.diam - 1 + indepNeighborsCard G u ≤ G.largestInducedBipartiteSubgraphSize := by
  obtain ⟨x, y, hxy⟩ := G.exists_dist_eq_diam
  rcases le_total (G.dist u y) (G.dist u x) with hba | hab
  · exact diam_sub_one_add_indepNeighborsCard_le_bipartite_aux G hconn u x y hxy hba helt
  · rw [G.dist_comm] at hxy
    exact diam_sub_one_add_indepNeighborsCard_le_bipartite_aux G hconn u y x hxy hab helt

/--
WOWII [Conjecture 19](http://cms.dt.uh.edu/faculty/delavinae/research/wowII/)

If `G` is connected then the size `b(G)` of a largest induced bipartite subgraph
satisfies
`b(G) ≥ FLOOR((∑ ecc(v))/(|V|) + sSup (range (l G)))`, where `ecc(v)` denotes
eccentricity and `l(G)` is the independence number of neighbourhoods.
-/
@[category research solved, AMS 5]
theorem conjecture19 (G : SimpleGraph α) [Nontrivial α] (h_conn : G.Connected) :
    ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) +
      sSup (Set.range (indepNeighbors G))⌋ ≤ b G := by
  obtain ⟨u, _, hsup⟩ := exists_max_indepNeighborsCard_and_csSup_eq G
  rw [hsup, b,
    show (G.largestInducedBipartiteSubgraphSize : ℝ) = ((G.largestInducedBipartiteSubgraphSize : ℤ) : ℝ) by push_cast; rfl,
    Int.cast_le]
  set e := (G.eccent u).toNat
  set D := G.diam
  set L := indepNeighborsCard G u
  have hcard_pos : (0 : ℝ) < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
  by_cases hDe : D ≤ e
  · have hsum_le : ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ) ≤
        (Fintype.card α : ℝ) * (e : ℝ) := by
      calc ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)
          ≤ ∑ _v ∈ Finset.univ, (e : ℝ) := by
            apply Finset.sum_le_sum
            intro v _
            have hv : (G.eccent v).toNat ≤ e := le_trans (eccent_toNat_le_diam h_conn v) hDe
            exact_mod_cast hv
        _ = (Fintype.card α : ℝ) * (e : ℝ) := by simp
    have hdiv_le : (∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) + (L : ℝ) ≤
        ((e + L : ℕ) : ℝ) := by
      have hdiv : (∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) ≤ (e : ℝ) :=
        (div_le_iff₀ hcard_pos).mpr (by linarith)
      push_cast
      linarith
    have hfloor_le : ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) + (L : ℝ)⌋ ≤
        ((e + L : ℕ) : ℤ) := by
      have hmono := Int.floor_mono hdiv_le
      rwa [show (((e + L : ℕ) : ℝ)) = (((e + L : ℕ) : ℤ) : ℝ) by push_cast; rfl,
        Int.floor_intCast] at hmono
    have hb_ge := eccent_toNat_add_indepNeighborsCard_le_bipartite G h_conn u
    omega
  · push Not at hDe
    have hsum_lt : ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ) <
        (Fintype.card α : ℝ) * (D : ℝ) := by
      calc ∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)
          < ∑ _v ∈ Finset.univ, (D : ℝ) := by
            apply Finset.sum_lt_sum
            · intro v _
              exact_mod_cast eccent_toNat_le_diam h_conn v
            · refine ⟨u, Finset.mem_univ u, ?_⟩
              exact_mod_cast hDe
        _ = (Fintype.card α : ℝ) * (D : ℝ) := by simp
    have hdiv_lt : (∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) + (L : ℝ) <
        (((D + L : ℕ) : ℤ) : ℝ) := by
      have hdiv : (∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) < (D : ℝ) :=
        (div_lt_iff₀ hcard_pos).mpr (by linarith)
      push_cast
      linarith
    have hfloor_lt : ⌊(∑ v ∈ Finset.univ, ((G.eccent v).toNat : ℝ)) / (Fintype.card α : ℝ) + (L : ℝ)⌋ <
        ((D + L : ℕ) : ℤ) :=
      Int.floor_lt.mpr hdiv_lt
    have hb_ge := diam_sub_one_add_indepNeighborsCard_le_bipartite G h_conn u hDe
    omega

-- Sanity checks

/-- The size of a largest induced bipartite subgraph is always nonnegative. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ G.largestInducedBipartiteSubgraphSize :=
  Nat.zero_le _

/-- The real-valued largest induced bipartite subgraph invariant `b G` is nonnegative. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) : 0 ≤ b G := by
  unfold b
  positivity

/-- The local independence number `indepNeighbors G v` is always nonnegative. -/
@[category test, AMS 5]
example (G : SimpleGraph (Fin 3)) (v : Fin 3) : 0 ≤ indepNeighbors G v := by
  unfold indepNeighbors
  positivity

end WrittenOnTheWallII.GraphConjecture19
