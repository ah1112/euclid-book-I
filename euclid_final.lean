/-
Copyright (c) 2022 André Hernandez-Espiet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : André Hernandez-Espiet
-/

import data.set.finite
import tactic.linarith

/-!
# Synthetic Geometry, Euclid's Elements Book I using Avigad Axioms
In this file we ...

## Main definitions
* `incidence_geometry` : class containing axioms...

## Main results
* `pythagorean_theorem` : The Pythagorean theorem
## Tags
synthetic geometry, Euclid elements
-/

universes u1 u2 u3 u4 u5 u6
class incidence_geometry :=
(point : Type u1)
(line : Type u2)
(circle : Type u3)
(length_type : Type u4)
(angle_type : Type u5)
(area_type : Type u6)
[len_ins : linear_ordered_comm_ring length_type]
[angle_ins : linear_ordered_comm_ring angle_type]
[area_ins : linear_ordered_comm_ring area_type]
(online : point → line → Prop)
(B : point → point → point → Prop) -- Betweenness
(sameside : point → point → line → Prop)
(center_circle : point → circle → Prop)
(in_circle : point → circle → Prop)
(on_circle : point → circle → Prop)
(lines_inter : line → line → Prop)
(line_circle_inter : line → circle → Prop)
(circles_inter : circle → circle → Prop)
(length : point → point → length_type)
(angle : point → point → point → angle_type)
(rightangle : angle_type)
(area : point → point → point → area_type)

(more_pts : ∀ (S : set point), S.finite → ∃ (a : point), a ∉ S)
(pt_B_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b a c)
(pt_extension_of_ne : ∀ {b c : point}, b ≠ c → ∃ (a : point), B b c a)
(diffside_of_not_online : ∀ {L : line}, ∀ {a : point}, ¬online a L →
  ∃ (b : point), ¬online b L ∧ ¬sameside a b L)
(line_of_pts : ∀ (a b : point), ∃ (L : line), online a L ∧ online b L)
(circle_of_ne : ∀ {a b : point}, a ≠ b → ∃ (α : circle), center_circle a α ∧ on_circle b α)
(pt_of_lines_inter : ∀ {L M : line}, lines_inter L M → ∃ (a : point), online a L ∧ online a M)
(pts_of_line_circle_inter : ∀ {L : line}, ∀ {α : circle}, line_circle_inter L α →
  ∃ (a b : point), a ≠ b ∧ online a L ∧ online b L ∧ on_circle a α ∧ on_circle b α)
(pt_oncircle_of_inside_outside : ∀ {b c : point}, ∀ {α : circle}, ¬on_circle c α → in_circle b α →
  ¬in_circle c α → ∃ (a : point), B b a c ∧ on_circle a α)
(pt_oncircle_of_inside_ne : ∀ {a b : point}, ∀ {α : circle}, a ≠ b → in_circle b α →
  ∃ (c : point), B a b c ∧ on_circle c α)
(pts_of_circles_inter : ∀ {α β : circle}, circles_inter α β →
  ∃ (a b : point), a ≠ b ∧ on_circle a α ∧ on_circle a β ∧ on_circle b α ∧ on_circle b β)
(pt_sameside_of_circles_inter : ∀ {b c d : point}, ∀ {L : line}, ∀ {α β : circle},
  online c L → online d L → ¬online b L → center_circle c α → center_circle d β → circles_inter α β
  → ∃ (a : point), sameside a b L ∧ on_circle a α ∧ on_circle a β)
(line_unique_of_pts : ∀ {a b : point}, ∀ {L M : line}, a ≠ b → online a L → online b L →
  online a M → online b M → L = M)
(center_circle_unique : ∀ {a b : point}, ∀ {α : circle}, center_circle a α → center_circle b α →
  a = b)
(inside_circle_of_center : ∀ {a : point}, ∀ {α : circle}, center_circle a α → in_circle a α)
(not_oncircle_of_inside : ∀ {a : point}, ∀ {α : circle}, in_circle a α → ¬on_circle a α)
(B_symm : ∀ {a b c : point}, B a b c → B c b a)
(ne_12_of_B : ∀ {a b c : point}, B a b c → a ≠ b)
(ne_13_of_B : ∀ {a b c : point}, B a b c → a ≠ c)
(ne_23_of_B : ∀ {a b c : point}, B a b c → b ≠ c)
(not_B_of_B : ∀ {a b c : point}, B a b c → ¬B b a c)
(online_3_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online b L → online c L)
(online_2_of_B : ∀ {a b c : point}, ∀ {L : line}, B a b c → online a L → online c L → online b L)
(B124_of_B134_B123 : ∀ {a b c d : point}, B a b c → B a d b → B a d c)
(B124_of_B123_B234 : ∀ {a b c d : point}, B a b c → B b c d → B a b d)
(B_of_three_online_ne : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → b ≠ c → online a L →
  online b L → online c L → B a b c ∨ B b a c ∨ B a c b)
(not_B324_of_B123_B124 : ∀ {a b c d : point}, B a b c → B a b d → ¬B c b d)
(sameside_rfl_of_not_online : ∀ {a : point}, ∀ {L : line}, ¬online a L → sameside a a L)
(sameside_symm : ∀ {a b : point}, ∀ {L : line}, sameside a b L → sameside b a L)
(not_online_of_sameside : ∀ {a b : point}, ∀ {L : line}, sameside a b L → ¬online a L)
(sameside_trans : ∀ {a b c : point}, ∀ {L : line}, sameside a b L → sameside a c L → sameside b c L)
(sameside_or_of_diffside : ∀ {a b c : point}, ∀ {L : line}, ¬online a L → ¬online b L →
  ¬online c L → ¬sameside a b L → sameside a c L ∨ sameside b c L)
(sameside12_of_B123_sameside13 : ∀ {a b c : point}, ∀ {L : line}, B a b c → sameside a c L →
  sameside a b L)
(sameside23_of_B123_online1_not_online2 : ∀ {a b c : point}, ∀ {L : line}, online a L →
  ¬online b L → B a b c → sameside b c L)
(not_sameside13_of_B123_online2 : ∀ {a b c : point}, ∀ {L : line}, online b L → B a b c →
  ¬sameside a c L)
(B_of_online_inter : ∀ {a b c : point}, ∀ {L M : line}, a ≠ b → b ≠ c → a ≠ c → L ≠ M →
  online a M → online b M → online c M → online b L → ¬sameside a c L → B a b c)
(not_sameside_of_sameside_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, online a L →
  online a M → online a N → online b L → online c M → online d N → sameside c d L →
  sameside b c N → ¬sameside b d M)
(sameside_of_sameside_not_sameside : ∀ {a b c d : point}, ∀ {L M N : line}, a ≠ b → online a L →
  online a M → online a N → online b L → online c M → online d N → ¬online d M → sameside c d L →
  ¬sameside b d M → sameside b c N)
(B_of_line_circle_inter : ∀ {a b c : point}, ∀ {L : line}, ∀ {α : circle}, b ≠ c →
  online a L → online b L → online c L → on_circle b α → on_circle c α → in_circle a α → B b a c)
(not_sameside_of_circle_inter : ∀ {a b c d : point}, ∀ {L : line}, ∀ {α β : circle}, c ≠ d →
  α ≠ β → online a L → online b L → center_circle a α → center_circle b β → on_circle c α →
  on_circle c β → on_circle d α → on_circle d β → circles_inter α β → ¬sameside c d L)
(lines_inter_of_not_sameside : ∀ {a b : point}, ∀ {L M : line}, online a M → online b M →
  ¬sameside a b L → lines_inter L M)
(line_circle_inter_of_not_sameside : ∀ {a b : point}, ∀ {L : line}, ∀ {α : circle}, ¬sameside a b L
  → on_circle a α ∨ in_circle a α → on_circle b α ∨ in_circle b α → line_circle_inter L α)
(line_circle_inter_of_inside_online : ∀ {a : point}, ∀ {L : line}, ∀ {α : circle}, online a L →
  in_circle a α → line_circle_inter L α)
(circles_inter_of_inside_oncircle : ∀ {a b : point}, ∀ {α β : circle}, on_circle b α →
  on_circle a β → in_circle a α → in_circle b β → circles_inter α β)
(length_eq_zero_iff : ∀ {a b : point}, length a b = 0 ↔ a = b)
(length_symm : ∀ (a b : point), length a b = length b a)
(angle_symm : ∀ (a b c : point), angle a b c = angle c b a)
(angle_nonneg : ∀ (a b c : point), 0 ≤ angle a b c)
(length_nonneg : ∀ (a b : point), 0 ≤ length a b)
(degenerate_area : ∀ (a b : point), area a a b = 0)
(area_invariant : ∀ (a b c : point), area a b c = area c a b ∧ area a b c = area a c b)
(area_eq_of_SSS : ∀ {a b c a1 b1 c1 : point}, length a b = length a1 b1 →
  length b c = length b1 c1 → length c a = length c1 a1 → area a b c = area a1 b1 c1)
(length_sum_of_B : ∀ {a b c : point}, B a b c → length a b + length b c = length a c)
(oncircle_iff_length_eq : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → on_circle b α →
  (length a b = length a c ↔ on_circle c α))
(incircle_iff_length_lt : ∀ {a b c : point}, ∀ {α : circle}, center_circle a α → on_circle b α →
  (length a c < length a b ↔ in_circle c α))
(angle_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → a ≠ c → online a L → online b L →
  (online c L ∧ ¬B b a c ↔ angle b a c = 0))
(angle_add_iff_sameside : ∀ {a b c d : point}, ∀ {L M : line}, a ≠ b → a ≠ c → L ≠ M → online a L →
  online b L → online a M → online c M → ¬online d M → ¬online d L →
  (angle b a c = angle b a d + angle d a c ↔ sameside b d M ∧ sameside c d L))
(angle_eq_iff_rightangle : ∀ {a b c d : point}, ∀ {L : line}, online a L → online b L →
  ¬online d L → B a c b → (angle a c d = angle d c b ↔ angle a c d = rightangle))
(angle_extension : ∀ {a b c a1 b1 c1 : point}, ∀ {L M : line}, b ≠ a → b1 ≠ a → c ≠ a → c1 ≠ a →
  online a L → online b L → online b1 L → online a M → online c M → online c1 M → ¬B b a b1 →
  ¬B c a c1 → angle b a c = angle b1 a1 c1)
(unparallel_postulate : ∀ {a b c d : point}, ∀ {L M N : line}, b ≠ c → online a L → online b L →
  online b M → online c M → online c N → online d N →  sameside a d M →
  angle a b c + angle b c d < 2 * rightangle →
  ∃ (e : point), online e L ∧ online e N ∧ sameside e a M)
(area_zero_iff_online : ∀ {a b c : point}, ∀ {L : line}, a ≠ b → online a L → online b L →
  (area a b c = 0 ↔ online c L))
(area_add_iff_B : ∀ {a b c d : point}, ∀ {L : line}, a ≠ b → b ≠ c → c ≠ a → online a L →
  online b L → online c L → ¬online d L → (B a c b ↔ area a c d + area d c b = area a d b))
(SAS_iff_SSS : ∀ {a b c d e f : point}, length a b = length d e → length a c = length d f →
  (angle b a c = angle e d f ↔ length b c = length e f)) --Euclid Prop 4, 8

open incidence_geometry

variables [i : incidence_geometry] {a b c d e f g h j k l : i.point} {L M N O P Q : i.line}
  {α β : i.circle} {la : length_type}

attribute [instance] incidence_geometry.len_ins
attribute [instance] incidence_geometry.angle_ins
attribute [instance] incidence_geometry.area_ins

include i

-------------------------------------------------- Definitions -------------------------------------
def diffside (a b : point) (L : line) := ¬online a L ∧ ¬online b L ∧ ¬sameside a b L
--3/28/23
def out_circle (a : point) (α : circle) := ¬on_circle a α ∧ ¬in_circle a α

def colinear (a b c : point) := ∃ L : line, online a L ∧ online b L ∧ online c L

def triangle (a b c : point) := ¬colinear a b c

def eq_tri (a b c : point) := triangle a b c ∧ length a b = length a c ∧ length b a = length b c
  ∧ length c a = length c b
-------------------------------------------------- API ---------------------------------------------
theorem online_of_line (L : line) : ∃ (a : point), online a L :=
  by rcases more_pts ∅ set.finite_empty with ⟨a, -⟩; exact classical.by_cases
  (λ aL, by use a; exact aL) (λ aL, by rcases diffside_of_not_online aL with ⟨b, -, abL⟩;
  rcases line_of_pts a b with ⟨M, aM, bM⟩; rcases pt_of_lines_inter
  (lines_inter_of_not_sameside aM bM abL) with ⟨c, cL, -⟩; exact ⟨c, cL⟩)

theorem online_ne_of_line (L : line) : ∃ (a b : point), a ≠ b ∧ online a L ∧ online b L :=
  by rcases online_of_line L with ⟨a, aL⟩; rcases more_pts {a} (set.finite_singleton a) with ⟨b, hb⟩;
  rcases circle_of_ne (by refine ne_of_mem_of_not_mem (set.mem_singleton a) hb) with ⟨α, acen, -⟩;
  rcases pts_of_line_circle_inter (line_circle_inter_of_inside_online aL
  (inside_circle_of_center acen)) with ⟨c, d, cd, cL, dL, -, -⟩; exact ⟨c, d, cd, cL, dL⟩

lemma len_pos_of_nq (ab : a ≠ b) : 0 < length a b :=
  (ne.symm (not_imp_not.mpr length_eq_zero_iff.mp ab)).le_iff_lt.mp (length_nonneg a b)

theorem ne_of_ne_len (ab : a ≠ b) (ab_cd : length a b = length c d) : c ≠ d :=
  λ ac, by linarith[length_eq_zero_iff.mpr ac, len_pos_of_nq ab]

theorem ne_of_ne_len' (cd : c ≠ d) (ab_cd : length a b = length c d) : a ≠ b := --3/28/23
  ne_of_ne_len cd (ab_cd.symm)

theorem length_sum_perm_of_B (Babc : B a b c) : 0 < length a b ∧ 0 < length b a ∧ 0 < length b c
  ∧ 0 < length c b ∧ 0 < length a c ∧ 0 < length c a ∧ length a b + length b c = length a c ∧
  length b a + length b c = length a c ∧ length b a + length c b = length a c ∧
  length b a + length b c = length c a ∧ length b a + length c b = length c a ∧
  length a b + length c b = length a c ∧ length a b + length b c = length c a ∧
  length a b + length c b = length c a :=
⟨len_pos_of_nq (ne_12_of_B Babc), by linarith[length_symm a b,
  len_pos_of_nq (ne_12_of_B Babc)], len_pos_of_nq (ne_23_of_B Babc), by linarith[length_symm b c,
  len_pos_of_nq (ne_23_of_B Babc)], len_pos_of_nq (ne_13_of_B Babc), by linarith[length_symm a c,
  len_pos_of_nq (ne_13_of_B Babc)], by repeat {split}; repeat {linarith[length_sum_of_B Babc,
  length_symm a b, length_symm a c, length_symm b c]}⟩

theorem length_perm_of_3pts (a b c : point) : length a b = length b a ∧ length a c = length c a ∧
  length b c = length c b := ⟨length_symm a b, length_symm a c, length_symm b c⟩

theorem not_online_of_line (L : line) : ∃ (a : point), ¬online a L :=
  by rcases online_ne_of_line L with ⟨b, c, bc, bL, cL⟩; rcases circle_of_ne bc with ⟨α, bα, cα⟩;
  rcases circle_of_ne bc.symm with ⟨β, cβ, bβ⟩; rcases pts_of_circles_inter
  (circles_inter_of_inside_oncircle cα bβ (inside_circle_of_center bα) (inside_circle_of_center
  cβ)) with ⟨a, -, -, aα, aβ, -, -⟩; have bc_ba := (oncircle_iff_length_eq bα cα).mpr aα;
  have cb_ca := (oncircle_iff_length_eq cβ bβ).mpr aβ; exact ⟨a, λ aL, ((by push_neg; repeat
  {split}; repeat {exact (λ Bet, by linarith[length_sum_perm_of_B Bet])}) : ¬ (B b c a ∨ B c b a ∨
  B b a c)) (B_of_three_online_ne bc (ne_of_ne_len bc bc_ba)(ne_of_ne_len bc.symm cb_ca) bL cL aL)⟩

theorem online_of_circles_inter (aα : center_circle a α) (bβ : center_circle b β)
  (αβ : circles_inter α β) : ∃ (c : point) (L : line), online a L ∧ online b L ∧ on_circle c α ∧
  on_circle c β ∧ ¬online c L :=
by rcases line_of_pts a b with ⟨L, aL, bL⟩; rcases not_online_of_line L with ⟨d, dL⟩;
  rcases pt_sameside_of_circles_inter aL bL dL aα bβ αβ with ⟨c, cdL, cα, cβ⟩;
  exact ⟨c, L, aL, bL, cα, cβ, not_online_of_sameside cdL⟩

theorem not_sameside_symm (abL : ¬sameside a b L) : ¬sameside b a L := λ baL,
  abL (sameside_symm baL)

lemma diffside_symm (abL : diffside a b L) : diffside b a L :=
  ⟨abL.2.1, abL.1, (not_sameside_symm abL.2.2)⟩

theorem diffside_of_sameside_diffside (abL : sameside a b L) (acL : diffside a c L) :
  diffside b c L :=
by by_contra; unfold diffside at h; push_neg at h; exact acL.2.2
  (sameside_trans (sameside_symm abL) (h (not_online_of_sameside (sameside_symm abL)) acL.2.1))

theorem diffside_of_circles_inter (aα : center_circle a α) (bβ : center_circle b β)
  (αβ : circles_inter α β) : ∃ (c d : point) (L : line), online a L ∧ online b L ∧ on_circle c α ∧
  on_circle c β ∧ on_circle d α ∧ on_circle d β ∧ diffside c d L :=
by rcases online_of_circles_inter aα bβ αβ with ⟨c, L, aL, bL, cα, cβ, cL⟩;
  rcases diffside_of_not_online cL with ⟨e, eL, ceL⟩; rcases pt_sameside_of_circles_inter aL bL eL
  aα bβ αβ with ⟨d, deL, dα, dβ⟩; exact ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, diffside_symm
  (diffside_of_sameside_diffside (sameside_symm deL) ⟨eL, cL, not_sameside_symm ceL⟩)⟩

theorem online_of_3_2_online (ab : a ≠ b) (aL : online a L) (bL : online b L) (cL : online c L)
  (aM : online a M) (bM : online b M) : online c M := by rwa line_unique_of_pts ab aL bL aM bM at cL

theorem triangle_of_ne_online (ab : a ≠ b) (aL : online a L) (bL : online b L) (cL : ¬online c L) :
  triangle a b c :=
λ col, by rcases col with ⟨M, aM, bM, cM⟩; exact cL (online_of_3_2_online ab aM bM cM aL bL)

theorem eq_tri_of_length_online (ab : a ≠ b) (aL : online a L) (bL : online b L) (cL : ¬online c L)
  (ab_ac : length a b = length a c) (bc_ba : length b c = length b a) : eq_tri a b c :=
⟨triangle_of_ne_online ab aL bL cL, by repeat {split}; linarith[length_perm_of_3pts a b c]⟩
--3/23/23
theorem B_circ_of_ne (ab : a ≠ b) (bc : b ≠ c) : ∃ (d : point) (α : circle), B a b d ∧
  center_circle b α ∧ on_circle c α ∧ on_circle d α :=
by rcases circle_of_ne bc with ⟨α, bα, cα⟩; rcases pt_oncircle_of_inside_ne ab
  (inside_circle_of_center bα) with ⟨d, Babd, dα⟩; exact ⟨d, α, Babd, bα, cα, dα⟩

theorem online_of_eq (ab : a = b) (aL : online a L) : online b L := by rwa ab at aL

theorem online_of_eq' (ab : a = b) (bL : online b L) : online a L := by rwa ab.symm at bL

theorem ne_23_of_tri (tri: triangle a b c) : b ≠ c :=
  λ bc, by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq bc bL⟩

theorem ne_32_of_tri (tri : triangle a b c) : c ≠ b := λ cb, (ne_23_of_tri tri) cb.symm

theorem ne_13_of_tri (tri : triangle a b c) : a ≠ c :=
  λ ac, by rcases line_of_pts a b with ⟨L, aL, bL⟩; exact tri ⟨L, aL, bL, online_of_eq ac aL⟩

theorem ne_31_of_tri (tri : triangle a b c) : c ≠ a := λ ca, (ne_13_of_tri tri) ca.symm

theorem incirc_of_lt (aα : center_circle a α) (bα : on_circle b α)
  (ac_ab : length a c < length a b) : in_circle c α := (incircle_iff_length_lt aα bα).mp ac_ab

theorem B_circ_out_of_B (ab : a ≠ b) (Bacd : B a c d) (ab_ac : length a b = length a c) :
  ∃ (e : point) (α : circle), B a b e ∧ center_circle a α ∧ on_circle d α ∧ on_circle e α :=
by rcases circle_of_ne (ne_13_of_B Bacd) with ⟨α, aα, dα⟩; rcases pt_oncircle_of_inside_ne ab
  (incirc_of_lt aα dα (by linarith[length_sum_perm_of_B Bacd] : length a b < length a d)) with
  ⟨e, Babe, eα⟩; exact ⟨e, α, Babe, aα, dα, eα⟩

theorem length_eq_of_oncircle (aα : center_circle a α) (bα : on_circle b α) (cα : on_circle c α) :
   length a b = length a c := (oncircle_iff_length_eq aα bα).mpr cα
--3/28/23
theorem oncircle_of_oncircle_length (aα : center_circle a α) (bα : on_circle b α)
  (ab_ac : length a b ≠ length a c) : ¬on_circle c α := λ cα, ab_ac (length_eq_of_oncircle aα bα cα)
--3/28/23
theorem incircle_of_oncircle_length (aα : center_circle a α) (bα : on_circle b α)
  (ab_ac : length a b ≤ length a c) : ¬in_circle c α :=
λ c_in_α, by linarith[(incircle_iff_length_lt aα bα).mpr c_in_α]

theorem length_eq_of_B_B (Bdbe: B d b e) (Bdaf : B d a f) (da_db : length d a = length d b)
  (de_df : length d e = length d f):
length a f = length b e := by linarith[length_sum_perm_of_B Bdbe, length_sum_perm_of_B Bdaf]

theorem B_oncircle_of_inside_outside (a_in_α : in_circle a α) (b_out_α : out_circle b α) :
  ∃ (c : point), B a c b ∧ on_circle c α :=
pt_oncircle_of_inside_outside b_out_α.1 a_in_α b_out_α.2
--3/28/23
theorem out_circle_of_lt (aα : center_circle a α) (bα : on_circle b α)
  (ab_lt_ac : length a b < length a c) : out_circle c α :=
⟨oncircle_of_oncircle_length aα bα (by linarith), incircle_of_oncircle_length aα bα (by linarith)⟩
--------------------------------------------Euclid--------------------------------------------------
              /-- Euclid I.1, construction of two equilateral triangles -/
theorem iseqtri_iseqtri_diffside_of_ne (ab : a ≠ b) : ∃ (c d : point), ∃ (L : line), online a L ∧
  online b L ∧ diffside c d L ∧ eq_tri a b c ∧ eq_tri a b d :=
begin
  rcases circle_of_ne ab with ⟨α, aα, bα⟩,
  rcases circle_of_ne (ne.symm ab) with ⟨β, bβ, aβ⟩,
  rcases diffside_of_circles_inter aα bβ  (circles_inter_of_inside_oncircle bα aβ
    (inside_circle_of_center aα) (inside_circle_of_center bβ)) with
    ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, cdL⟩,
  have ab_ac := (oncircle_iff_length_eq aα bα).mpr cα,
  have bc_ba := (oncircle_iff_length_eq bβ cβ).mpr aβ,
  have ab_ad := (oncircle_iff_length_eq aα bα).mpr dα,
  have bd_ba := (oncircle_iff_length_eq bβ dβ).mpr aβ,
  exact ⟨c, d, L, aL, bL, cdL, eq_tri_of_length_online ab aL bL cdL.1 ab_ac bc_ba,
    eq_tri_of_length_online ab aL bL cdL.2.1 ab_ad bd_ba⟩,
end

theorem iseqtri_iseqtri_diffside_of_ne' (ab : a ≠ b) : ∃ (c d : point), ∃ (L : line), online a L ∧
  online b L ∧ diffside c d L ∧ eq_tri a b c ∧ eq_tri a b d :=
begin
  rcases circle_of_ne ab with ⟨α, aα, bα⟩,
  rcases circle_of_ne (ne.symm ab) with ⟨β, bβ, aβ⟩,
  rcases diffside_of_circles_inter aα bβ  (circles_inter_of_inside_oncircle bα aβ
    (inside_circle_of_center aα) (inside_circle_of_center bβ)) with
    ⟨c, d, L, aL, bL, cα, cβ, dα, dβ, cdL⟩,
  --use [c, d, L],
  refine ⟨c, d, L, aL, bL, cdL, _⟩,
  split,
  {
    exact eq_tri_of_length_online ab aL bL cdL.1 ((oncircle_iff_length_eq aα bα).mpr cα)
      ((oncircle_iff_length_eq bβ cβ).mpr aβ),
  },
  have ab_ac := (oncircle_iff_length_eq aα bα).mpr cα,
  have bc_ba := (oncircle_iff_length_eq bβ cβ).mpr aβ,
  have ab_ad := (oncircle_iff_length_eq aα bα).mpr dα,
  have bd_ba := (oncircle_iff_length_eq bβ dβ).mpr aβ,
  exact ⟨c, d, L, aL, bL, cdL, eq_tri_of_length_online ab aL bL cdL.1 ab_ac bc_ba,
    eq_tri_of_length_online ab aL bL cdL.2.1 ab_ad bd_ba⟩,
end
--3/23/23
              /-- Euclid I.1, construction of a single equilateral triangle -/
theorem iseqtri_of_ne (ab : a ≠ b) : ∃ (c : point), eq_tri a b c :=
  by rcases iseqtri_iseqtri_diffside_of_ne ab with ⟨c, -, -, -, -, -, eqtri, -⟩; exact ⟨c, eqtri⟩
                          /-- Euclid I.2, collapsing compass -/
theorem length_eq_of_ne (a : point) (bc : b ≠ c) : ∃ (f : point), length a f = length b c :=
begin
  by_cases ab : a = b, rw ab; exact ⟨c, rfl⟩, --degenerate case
  rcases iseqtri_of_ne ab with ⟨d, eqtri⟩,
  rcases B_circ_of_ne (ne_32_of_tri eqtri.1) bc with ⟨e, α, Bdbe, bα, cα, eα⟩,
  rcases B_circ_out_of_B (ne_31_of_tri eqtri.1) Bdbe eqtri.2.2.2 with ⟨f, β, Bdaf, dβ, eβ, fβ⟩,
  have be_bc := (length_eq_of_oncircle bα cα eα).symm,
  have de_df := length_eq_of_oncircle dβ eβ fβ,
  have af_be := length_eq_of_B_B Bdbe Bdaf eqtri.2.2.2 de_df,
  exact ⟨f, af_be.trans be_bc⟩, --calc block?
end

theorem length_eq_of_ne' (a : point) (bc : b ≠ c) : ∃ (f : point), length a f = length b c :=
begin
  by_cases ab : a = b, rw ab; exact ⟨c, rfl⟩, --degenerate case
  rcases iseqtri_of_ne ab with ⟨d, eqtri⟩,
  rcases B_circ_of_ne (ne_32_of_tri eqtri.1) bc with ⟨e, α, Bdbe, bα, cα, eα⟩,
  rcases B_circ_out_of_B (ne_31_of_tri eqtri.1) Bdbe eqtri.2.2.2 with ⟨f, β, Bdaf, dβ, eβ, fβ⟩,
  have de_df := length_eq_of_oncircle dβ eβ fβ,
  use f,
  calc length a f = length b e : length_eq_of_B_B Bdbe Bdaf eqtri.2.2.2 de_df
  ... = length b c : (length_eq_of_oncircle bα cα eα).symm,
end
                          /-- Euclid I.2, generalization -/
theorem length_eq_B_of_ne (ab : a ≠ b) (bc : b ≠ c) :
  ∃ (d : point), B a b d ∧ length b c = length b d :=
by rcases B_circ_of_ne ab bc with ⟨d, α, Babd, bα, cα, dα⟩;
  exact ⟨d, Babd, length_eq_of_oncircle bα cα dα⟩
                          /-- Euclid I.2, generalization -/
theorem length_eq_B_of_ne_four (ab : a ≠ b) (cd : c ≠ d) :
  ∃ (f : point), B a b f ∧ length c d = length b f :=
begin
  rcases length_eq_of_ne b cd with ⟨e, be_cd⟩,
  rcases length_eq_B_of_ne ab (ne_of_ne_len' cd be_cd) with ⟨f, Babf, be_bf⟩,
  exact ⟨f, Babf, by linarith⟩,
end
                /-- Euclid I.3, Moving a smaller segment on top of a larger one -/
theorem B_length_eq_of_ne_lt (cd : c ≠ d) (cd_lt_ab : length c d < length a b) :
  ∃ (f : point), B a f b ∧ length a f = length c d :=
begin
  rcases length_eq_of_ne a cd with ⟨e, ae_cd⟩,
  rcases circle_of_ne (ne_of_ne_len' cd ae_cd) with ⟨α, aα, eα⟩, --combine into one line?
  rcases B_oncircle_of_inside_outside (inside_circle_of_center aα)
    (out_circle_of_lt aα eα (by rwa ← ae_cd at cd_lt_ab)) with ⟨f, Bafb, fα⟩,
  have ae_af := length_eq_of_oncircle aα eα fα,
  exact ⟨f, Bafb, by linarith⟩,
end
