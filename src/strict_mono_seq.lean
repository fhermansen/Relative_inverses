/-
Copyright (c) 2022 Flemming Hermansen. 
Released under Apache 2.0 license as described in 
https://www.apache.org/licenses/LICENSE-2.0
Authors: Flemming Hermansen
-/

import algebra.algebra.basic
import order.boolean_algebra
import order.partial_sups

/-
The main result of this file states that 
any Boolean algebra (B)
either has a finite set of atoms
or there exists an strictly increasing sequence of elements:
exists_fin_atomset_sup_top_of_not_strict_mono {B : Type*} [hB : boolean_algebra B] 
( no_inf_seq : ¬( ∃ (strict_mono_seq : ℕ → B), strict_mono strict_mono_seq ) ) : 

1. if there are infinitely many atoms then an increasing sequence of finite sets of atoms
is defined inductively by:
def atomset_of_n_aux {B : Type*} [hB : boolean_algebra B]
(h : ex_inf_atoms B) : ℕ → atomset_aux B
It is proved that the supremum of these finite sets gives a strictly increasing sequence.

2. If there, on the other hand, exists a maximal finite set of atoms (s) 
then the supremum of this set is examined:
2a. ⊔ s < ⊤: 
Then the complement is not equal to bottom, 
and there are no atoms less than or equal to this complement.
Then we define a sequence of strictly decreasing elements:
  def aux_sequence {B : Type*} [hB : boolean_algebra B] (e_init : B) 
  (h_na : not_bot_no_atoms_le e_init )
The complement gives a strictly increasing sequence.

2b:  ⊔ s = ⊤: We are done
-/

variables {B : Type*} [boolean_algebra B] 
{s : list B}

open_locale classical

noncomputable theory

def sup_list {B} [boolean_algebra B] : list B → B
| [] := ⊥
| (hd :: tl) := hd ⊔ sup_list tl

def not_bot_no_atoms_le (e) : Prop := ⊥ < e ∧ ∀ (e' : B), ⊥ < e' → e' ≤ e → ¬ ⊥ ⋖ e' 

def nb_lt {B} [hB : boolean_algebra B] (e' e : B) : Prop := ⊥ < e' ∧ e' < e

def nb_le {B} [hB : boolean_algebra B] (e' e : B) : Prop := ⊥ < e' ∧ e' ≤ e

lemma nb_lt_trans {b e : B} 
(h_nb_lt : nb_lt b e) (h_na_le : not_bot_no_atoms_le e) : not_bot_no_atoms_le b := 
begin
  cases h_nb_lt with h_nb_b h_b_lt_e,
  unfold not_bot_no_atoms_le, 
  unfold not_bot_no_atoms_le at h_na_le, 
  -- have h_nb_e : ⊥ < e, by exact lt_trans h_nb_b h_b_lt_e,
  split, assumption, 
  cases h_na_le with h_nb_e h_na_le,
  intros e', specialize h_na_le e',
  intros nb_e', specialize h_na_le nb_e',
  intros le_e'_b,
  have le_e'_e : e' ≤ e, by exact le_of_lt (gt_of_gt_of_ge h_b_lt_e le_e'_b),
  specialize h_na_le le_e'_e,
  assumption,
end

lemma nb_le_trans {b e : B} 
(h_nb_le : ⊥ < b ∧ b ≤ e) (h_na_le : not_bot_no_atoms_le e) : not_bot_no_atoms_le b := 
begin
  cases h_nb_le with h_nb_b h_b_le_e,
  unfold not_bot_no_atoms_le, 
  unfold not_bot_no_atoms_le at h_na_le, 
  -- have h_nb_e : ⊥ < e, by exact lt_trans h_nb_b h_b_lt_e,
  split, assumption, 
  cases h_na_le with h_nb_e h_na_le,
  intros e', specialize h_na_le e',
  intros nb_e', specialize h_na_le nb_e',
  intros le_e'_b,
  have le_e'_e : e' ≤ e, by exact (le_trans le_e'_b h_b_le_e),
  specialize h_na_le le_e'_e,
  assumption,
end

lemma ex_nb_lt_of_na_le [hB : boolean_algebra B] (e : B) 
(no_atoms_le : not_bot_no_atoms_le e ) 
: ∃ (e' : B), ⊥ < e' ∧ e' < e :=
begin
  -- First we generate (b : B), such that: nb_lt b e
  cases no_atoms_le with h_not_bot_e h_le_not_atom,
  have not_atom_self : ¬⊥ ⋖ e,
  begin
    specialize h_le_not_atom e h_not_bot_e le_rfl, assumption
  end,
  simp at not_atom_self,
  unfold is_atom at not_atom_self, push_neg at not_atom_self,
  rw bot_lt_iff_ne_bot at h_not_bot_e,
  specialize not_atom_self h_not_bot_e, -- ∃ (b : B), b < e ∧ b ≠ ⊥
  cases not_atom_self with b not_atom_self, 
  -- Now use b:
  use b,
  cases not_atom_self with b_lt_e nb_b,
  rw ← bot_lt_iff_ne_bot at nb_b, split, assumption, assumption,
end

lemma inf_incr_list_of_no_disj_atoms_aux' [hB : boolean_algebra B] (e : B) (s : list B)
(no_atoms_le : not_bot_no_atoms_le e ) 
: ∃ (e' : B), ⊥ < e' ∧ e' < e 
∧ ( not_bot_no_atoms_le e' ) :=
begin
  -- First we generate (e' : B), such that: nb_lt e' e
  have ex_nb_lt : ∃ (e' : B), ⊥ < e' ∧ e' < e, by exact ex_nb_lt_of_na_le e no_atoms_le,
  cases ex_nb_lt with e' ex_nb_lt, use e',
  have nb_lt_saved : ⊥ < e' ∧ e' < e, by assumption,
  cases ex_nb_lt with nb_e' lt_e'_e, split, assumption, split, assumption,
  -- goal : not_bot_no_atoms_le e'
  have nb_lt_b_e : nb_lt e' e, by exact  nb_lt_saved,
  by exact nb_lt_trans nb_lt_b_e no_atoms_le,
end

lemma sup_gt_of_disj {B : Type*} [hB : boolean_algebra B] {e e' : B}
(hnbot : e' ≠ ⊥) (h_disj : disjoint e e') : e < e ⊔ e' :=
begin
  -- We have a week form of distributivity with '≤' instead of '='.
  -- have week_distributivity : ( e' ⊓ e ) ⊔ (e' ⊓ e'') ≤  e' ⊓ (e ⊔ e''), by exact le_inf_sup,
  -- Trerefore, we do not get a contradiction from: 
  -- ⊥ = e' ⊓ e = e' ⊓ (e ⊔ e') =?= (e' ⊓ e) ⊔ (e' ⊓ e') = ⊥ ⊔ e' = e'
  unfold disjoint at h_disj, rw le_bot_iff at h_disj, rw inf_comm at h_disj, -- e' ⊓ e = ⊥
  by_contradiction h_contra', -- ¬e < e ⊔ e'
  have e_le_self_sup : e ≤ e ⊔ e', by exact le_sup_left,
  have h_contra : e = e ⊔ e', by exact eq_of_le_of_not_lt e_le_self_sup h_contra', -- e = e ⊔ e'
  have he'_le_sup_self : e' ≤ e ⊔ e', by exact le_sup_right,
  have h_inf_sup : e' ⊓ (e ⊔ e') = e', by exact inf_eq_left.mpr he'_le_sup_self, -- e' ⊓ (e ⊔ e') = e'
  rw ← h_contra at h_inf_sup, -- e' ⊓ e = e'
  rw h_disj at h_inf_sup, -- ⊥ = e'
  rw h_inf_sup at hnbot,
  contradiction,
end

lemma contra_pose_p {p1 p2 : Prop} : (p1 ↔ p2) ↔ (¬p1 ↔ ¬ p2) :=
begin
  split,
  begin -- → 
  intros h, 
    cases h with hp12 hp21,
    split, contrapose, push_neg, assumption, 
    contrapose, push_neg, assumption,
  end,
  -- ← 
  intros h,
    cases h with hp12 hp21,
    split, contrapose, assumption, 
    contrapose, assumption,
end

-- A one-line alternative tactic proof:
def contra_pose_p' {p1 p2 : Prop} : (p1 ↔ p2) ↔ (¬p1 ↔ ¬ p2) :=
begin
  split; intros h; cases h; split; contrapose; try {push_neg}; assumption, 
end

def are_atoms (s : finset B) := ∀ e ∈ s, ⊥ ⋖ e

def ex_atom_outside (s : finset B) := ∃ e, e ∉ s ∧ ⊥ ⋖ e

def ex_inf_atoms (B : Type*) [hB : boolean_algebra B] := ∀ (s : finset B), are_atoms s → ex_atom_outside s

lemma finset_induction (B : Type*) [hB : boolean_algebra B] (e : B) {s : finset B} (p : B → Prop) {hn : e ∉ s}
(ps : ∀  e' ∈ s , p e') (pe : p e) : ∀ e' ∈ (finset.cons e s hn) , p e' := 
begin 
  simp, split, assumption, assumption,
end

def boolean_algebra_finset_sup {B : Type*} [hB : boolean_algebra B] (s : finset B) : B :=
finset.fold (⊔) (⊥ : B) (λ e : B, e ) s

def mem_le_sup {B : Type*} [hB : boolean_algebra B] (s : finset B) := 
∀ (e : B), e ∈ s → e ≤ boolean_algebra_finset_sup s 

lemma le_sup0 (B : Type*) [hB : boolean_algebra B] :
mem_le_sup  (∅ : finset B) :=
begin
    intros e,
    have h_contra : e ∉ ∅, by exact set.not_mem_empty e,
    contradiction,
end

lemma le_sup_step {B : Type*} [hB : boolean_algebra B] ⦃e_new : B⦄ (s : finset B) (h : e_new ∉ s):
mem_le_sup s → mem_le_sup (finset.cons e_new s h) :=
begin
  intros h_mem_le_sup_s, 
  unfold mem_le_sup,
  intros e1 hi1, -- e1 ∈ finset.cons e_new s h
  have eq : finset.fold has_sup.sup ⊥ (λ (e : B), e) (finset.cons e_new s h) =
  e_new ⊔ (finset.fold has_sup.sup ⊥ (λ (e : B), e) s), by simp,
  unfold boolean_algebra_finset_sup,
  rw eq,
  rw finset.mem_cons at hi1,
  cases hi1,
  -- e1 = e
  rw hi1,
  exact le_sup_left,
  -- e1 ∈ s
  have h_e1_le : e1 ≤ boolean_algebra_finset_sup s, by exact h_mem_le_sup_s e1 hi1, -- exact hi1 e1 h,
  unfold boolean_algebra_finset_sup at h_e1_le,
  have h_s_le_sup : finset.fold has_sup.sup ⊥ (λ (e : B), e) s ≤ 
  e_new ⊔ finset.fold has_sup.sup ⊥ (λ (e : B), e) s, by exact le_sup_right,
  exact le_trans h_e1_le h_s_le_sup,
end

lemma members_lt_sup {B : Type*} [hB : boolean_algebra B] (s : finset B) (e : B)
(h_atoms : are_atoms s) (h_atom : ⊥ ⋖ e) : e ∈ s → mem_le_sup s :=
begin
  intros h_e_in_s,
  unfold mem_le_sup,
  exact @finset.cons_induction_on B (@mem_le_sup B hB) s (@le_sup0 B hB) (@le_sup_step B hB ),
end

structure atomset_aux (B : Type*) [hB : boolean_algebra B] := 
(s_old : finset B)
(s : finset B)
(e : B)
(h_e_in_s : e ∈ s)
(h_sub : s_old ⊂ s)
(h_disj : ∀ e' ∈ s_old, disjoint e' e)
(h_atoms : are_atoms s)

lemma eq_of_gt_bot_of_le_atom (e' e : B) (h_atom_e : ⊥ ⋖ e) 
(h_gt_bot : ⊥ < e') (hle : e' ≤ e) :
e' = e :=
begin
  unfold covby at h_atom_e, 
  --by_contradiction,
  let not_lt_atom' := (h_atom_e.right) h_gt_bot,
  exact eq_of_le_of_not_lt hle not_lt_atom',
end

lemma disj_of_ne_atoms {e' e : B} (h_atom_e' : ⊥ ⋖ e') (h_atom_e : ⊥ ⋖ e) 
(hne : e' ≠ e) :
(disjoint e' e) :=
begin
  unfold disjoint, 
  by_contradiction,
  have ne_bot : e' ⊓ e ≠ ⊥, by exact ne_of_not_le h,
  have ge_bot : ⊥ ≤ e' ⊓ e, simp,
  have gt_bot : ⊥ < e' ⊓ e, by exact lt_of_le_of_ne ge_bot ne_bot.symm,
  unfold covby at h_atom_e,   
  let not_lt_atom := (h_atom_e.right) gt_bot,
  have hle : e' ⊓ e ≤ e, by exact inf_le_right,
  have heq : e' ⊓ e = e, by exact eq_of_le_of_not_lt hle not_lt_atom,
  unfold covby at h_atom_e', 
  let not_lt_atom' := (h_atom_e'.right) gt_bot,
  have hle' : e' ⊓ e ≤ e', by exact inf_le_left,
  have heq' : e' ⊓ e = e', by exact eq_of_le_of_not_lt hle' not_lt_atom',
  rw heq at heq',
  rw heq' at hne,
  contradiction,
end

def atomset_of_n_0 {B : Type*} [hB : boolean_algebra B] (h : ex_inf_atoms B) :
 atomset_aux B :=
begin
  let s_old := @finset.empty B,
  have h_atoms : are_atoms s_old, 
  begin 
    unfold are_atoms,
    intros e h_mem,
    cases h_mem,
  end,
  let p := h s_old h_atoms,
  let e := (classical.some p),

    have he : e ∉ s_old ∧ ⊥ ⋖ e, by exact (classical.some_spec p),
    let s1 := (finset.cons e s_old he.left),
    have h_e_in_s1 : e ∈ s1, by exact finset.mem_cons_self e s_old,
    have hsub: s_old ⊂ s1, by exact finset.ssubset_cons he.left,
    have h_atoms1 : are_atoms s1,
    begin
      apply finset_induction, assumption, exact he.2,
    end,
    have disj : ∀ e' ∈ s_old, disjoint e' e,
    begin
      intros e' h',
      unfold are_atoms at h_atoms,
      let he'_atom := h_atoms e' h',
      apply disj_of_ne_atoms he'_atom he.2,
      by_contradiction,
      let h_contra := he.1,
      rw h at h',
      contradiction,
    end,
    exact ⟨ s_old, s1, e, h_e_in_s1, hsub, disj, h_atoms1 ⟩,
end

def atomset_of_n_step (aux : atomset_aux B) (h : ex_inf_atoms B) : 
atomset_aux B :=
begin
  let s := aux.s,
  let h_atoms := aux.h_atoms,
  let p := h s h_atoms,
  let e := (classical.some p),

    have he : e ∉ s ∧ ⊥ ⋖ e, by exact (classical.some_spec p),
    let s1 := (finset.cons e s he.left),
    have h_e_in_s1 : e ∈ s1, by exact finset.mem_cons_self e s,
    have hsub: s ⊂ s1, by exact finset.ssubset_cons he.left,
    have h_atoms1 : are_atoms s1,
    begin
      apply finset_induction, assumption, exact he.2,
    end,
    have disj : ∀ e' ∈ s, disjoint e' e,
    begin
      intros e' h',
      unfold are_atoms at h_atoms,
      let he'_atom := h_atoms e' h',
      apply disj_of_ne_atoms he'_atom he.2,
      by_contradiction,
      let h_contra := he.1,
      rw h at h',
      contradiction,
    end,
    exact ⟨ s, s1, e, h_e_in_s1, hsub, disj, h_atoms1 ⟩,
end

noncomputable
def atomset_of_n_aux {B : Type*} [hB : boolean_algebra B]
(h : ex_inf_atoms B) : ℕ → atomset_aux B
| 0 := atomset_of_n_0 h
| (n+1) := 
begin
  exact atomset_of_n_step (atomset_of_n_aux n) (h : ex_inf_atoms B),
end

def disj_atom_seq {B : Type*} [hB : boolean_algebra B] 
(h : ex_inf_atoms B) : 
ℕ → B :=
λ n, (atomset_of_n_aux h n).e

lemma atomset_of_n_aux_e_in_s_old1 {B : Type*} [hB : boolean_algebra B] 
(h : ex_inf_atoms B) (i : ℕ) :
(atomset_of_n_aux h i).e ∈ (atomset_of_n_aux h (i.succ)).s_old :=
begin
  have h_s_old : (atomset_of_n_aux h (i)).s =
  (atomset_of_n_aux h (i.succ)).s_old :=
  begin
    unfold atomset_of_n_aux atomset_of_n_step, 
  end,
  rw ← h_s_old,
  exact (atomset_of_n_aux h i).h_e_in_s,
end

lemma atomset_of_n_aux_subset_s_old {B : Type*} [hB : boolean_algebra B] 
(h : ex_inf_atoms B) (i : ℕ) :
(atomset_of_n_aux h i).s_old ⊂ (atomset_of_n_aux h (i.succ)).s_old :=
begin
  have h_s_old : (atomset_of_n_aux h (i)).s =
  (atomset_of_n_aux h (i.succ)).s_old :=
  begin
    unfold atomset_of_n_aux atomset_of_n_step, 
  end,
  rw ← h_s_old,
  exact (atomset_of_n_aux h i).h_sub,
end

lemma atomset_of_n_aux_subset_s {B : Type*} [hB : boolean_algebra B] 
(h : ex_inf_atoms B) (i : ℕ) :
(atomset_of_n_aux h i).s ⊂ (atomset_of_n_aux h (i.succ)).s :=
begin
  have h_s_old : (atomset_of_n_aux h (i)).s =
  (atomset_of_n_aux h (i.succ)).s_old :=
  begin
    unfold atomset_of_n_aux atomset_of_n_step, 
  end,
  rw h_s_old,
  exact (atomset_of_n_aux h i.succ).h_sub,
end

lemma atomset_of_n_aux_e_in_s_old {B : Type*} [hB : boolean_algebra B] 
(h : ex_inf_atoms B) {i j : ℕ} (hlt : i < j) :
(atomset_of_n_aux h i).e ∈ (atomset_of_n_aux h j).s_old :=
begin
  let hle := nat.succ_le_of_lt hlt,
  let h_e_in_s_old_succ := atomset_of_n_aux_e_in_s_old1 h i,
  let hsucc_add := nat.add_sub_of_le hle,
  rw ← hsucc_add,
  induction (j - i.succ) with j' hj,
  begin
    rw add_zero, exact atomset_of_n_aux_e_in_s_old1 h i,
  end,
  -- j'.succ:
  rw nat.add_succ,
  let gg := atomset_of_n_aux_subset_s_old h i,
  have h_subset : (atomset_of_n_aux h (i.succ + j')).s_old ⊂ (atomset_of_n_aux h ((i.succ + j').succ)).s_old,
  by exact atomset_of_n_aux_subset_s_old h (i.succ + j'),
  have h_sub : (atomset_of_n_aux h (i.succ + j')).s_old ⊆ (atomset_of_n_aux h (i.succ + j').succ).s_old, 
  by apply subset_of_ssubset h_subset,
  exact h_sub hj,
end

lemma disj_atom_seq_is_disjoint {B : Type*} [hB : boolean_algebra B] 
(h : ex_inf_atoms B) :
pairwise (disjoint on (disj_atom_seq h)) :=
begin
  rw pairwise_disjoint_on,
  intros m n hlt,
  unfold disj_atom_seq,
  have e_in_s1 : (atomset_of_n_aux h m).e ∈ (atomset_of_n_aux h n).s_old,
  by exact atomset_of_n_aux_e_in_s_old h hlt,
  let disj := (atomset_of_n_aux h n).h_disj (atomset_of_n_aux h m).e e_in_s1,
  exact disj,
end

def inc_atoms {B : Type*} [hB : boolean_algebra B] 
(h : ex_inf_atoms B) : ℕ → B :=
partial_sups (disj_atom_seq h)

lemma strict_mono_inc_atoms_step (h : ex_inf_atoms B) (i : ℕ) :
(inc_atoms (h : ex_inf_atoms B) i) < (inc_atoms (h : ex_inf_atoms B) i.succ) :=
begin
  have i_lt_i_succ : i < i.succ, by exact lt_add_one i,
  have h_disj_succ : disjoint (inc_atoms h i) (disj_atom_seq h i.succ),
  by exact partial_sups_disjoint_of_disjoint (disj_atom_seq h) (disj_atom_seq_is_disjoint h) i_lt_i_succ,
  have is_atom: ⊥ ⋖ disj_atom_seq h (i + 1),  
  by exact (atomset_of_n_aux h i.succ).h_atoms (atomset_of_n_aux h i.succ).e (atomset_of_n_aux h i.succ).h_e_in_s,
  have h_not_bot : disj_atom_seq h (i + 1) ≠ ⊥, by exact covby.ne' is_atom,
  exact sup_gt_of_disj h_not_bot h_disj_succ,
end

lemma strict_mono_inc_atoms' (h : ex_inf_atoms B)  (i j : ℕ) :
(inc_atoms (h : ex_inf_atoms B) i) < (inc_atoms (h : ex_inf_atoms B) (i + j.succ) ) := 
begin
  induction j,
  -- 0
  exact strict_mono_inc_atoms_step h i,
  -- j.succ
  let h_next :=  strict_mono_inc_atoms_step h (i + j_n).succ,
  rw nat.add_succ, rw nat.add_succ,
  exact lt_trans j_ih h_next,
end

lemma strict_mono_inc_atoms (h : ex_inf_atoms B) :
strict_mono (inc_atoms h) :=
begin
  intros i j hlt,
  let hle := nat.succ_le_of_lt hlt,
  have hsub : i.succ ≤ j → i.succ + (j - i.succ) = j, exact nat.add_sub_of_le,
  let j_eq := hsub hlt,
  rw ← j_eq,
  rw nat.succ_add,
  exact strict_mono_inc_atoms' h i (j - i.succ),
end

-------------------------- infinite increasing sequence from no atoms below
def p_aux (B : Type*) [hB : boolean_algebra B] (e e' : B): Prop := 
e' ≤  e

structure aux (B : Type*) [hB : boolean_algebra B] (e_init : B) :=
--(e_init : B)
(e_prev : B)
(e_free : B)
(h_lt : nb_lt e_free e_prev)
(h_le_init : e_free ≤ e_init) -- used for recursion in aux_step

def aux_init (B : Type*) [hB : boolean_algebra B] (e_init : B)
(h_na : not_bot_no_atoms_le e_init ) : aux B e_init :=
begin
  let e_prev := e_init,
  have ex_b_nb_lt : ∃ (b : B), nb_lt b e_prev, 
  by exact ex_nb_lt_of_na_le e_prev h_na,
  -- Does not work: cases ex_b_nb_lt with b nb_lt,
  -- instead, use classical.some and classical.some_spec
  let e_free := classical.some ex_b_nb_lt,
  have nb_lt_b_e : nb_lt e_free e_init, by exact classical.some_spec ex_b_nb_lt,
  let e_act := e_prev \ e_free,
  have h_lt : nb_lt e_free e_prev, by assumption,
  have h_le_init : e_free ≤ e_init, by exact le_of_lt nb_lt_b_e.2,
  exact {e_prev := e_prev, e_free := e_free,
  h_lt := h_lt, h_le_init := h_le_init},
end

def aux_step (B : Type*) [hB : boolean_algebra B] (e_init : B)
(h_na : not_bot_no_atoms_le e_init ) (a : aux B e_init): aux B e_init := 
begin
  let e_prev := a.e_free,
  --have fff : a.e_free ≤ e_init, by exact a.h_le_init,
  have h_nb_le : nb_le a.e_free e_init,
  begin
    unfold nb_le,
    cases a.h_lt with nb hlt,
    split, assumption, exact a.h_le_init,
  end,
  have h_na' : not_bot_no_atoms_le e_prev, 
  begin 
    exact nb_le_trans h_nb_le h_na,
  end,
  have ex_b_nb_lt : ∃ (b : B), nb_lt b e_prev, 
  by exact ex_nb_lt_of_na_le e_prev h_na',
  -- Does not work: cases ex_b_nb_lt with b nb_lt,
  -- instead, use classical.some and classical.some_spec
  let e_free := classical.some ex_b_nb_lt,
  have nb_lt_b_e : nb_lt e_free e_prev, by exact classical.some_spec ex_b_nb_lt,
  let e_act := e_prev \ e_free,
  have h_lt : nb_lt e_free a.e_free, by assumption,
  have h_le_init : e_free ≤ a.e_free, by exact le_of_lt nb_lt_b_e.2,
  have h_le_init : e_free ≤ e_init, 
  by exact le_trans (le_of_lt nb_lt_b_e.2) a.h_le_init,
  exact {e_prev := e_prev, e_free := e_free,
  h_lt := h_lt, h_le_init := h_le_init},
end

noncomputable
def aux_sequence {B : Type*} [hB : boolean_algebra B] (e_init : B) 
(h_na : not_bot_no_atoms_le e_init )
: ℕ → aux B e_init
| 0 := aux_init B e_init h_na
| (n+1) := aux_step B e_init h_na (aux_sequence n) -- Notice: n is the only parameter

lemma aux_decr1_e_free {B : Type*} [hB : boolean_algebra B] (e_init : B) 
(h_na : not_bot_no_atoms_le e_init ) (n : ℕ) : 
  (aux_sequence e_init h_na (n + 1 )).e_free <
  (aux_sequence e_init h_na n).e_free :=
  begin
    have prev_of_free : (aux_sequence e_init h_na (n + 1 )).e_prev =
    (aux_sequence e_init h_na n).e_free :=
    begin 
      unfold aux_sequence, unfold aux_step,
    end,
    rw ← prev_of_free,
    exact (aux_sequence e_init h_na (n + 1 )).h_lt.2,
  end

lemma aux_decr_k_e_free {B : Type*} [hB : boolean_algebra B] (e_init : B) 
(h_na : not_bot_no_atoms_le e_init ) (n : ℕ) : 
  --(aux_sequence e_init h_na n).e_init = e_init ∧ 
  --(aux_sequence e_init h_na n).e_free = (aux_sequence e_init h_na (n+1)).e_prev ∧ 
  ∀ (k : ℕ), 
  (aux_sequence e_init h_na (n + k + 1)).e_free <
  (aux_sequence e_init h_na n).e_free :=
begin
  intros k,
  induction k,
  begin -- k = 0 :
    exact aux_decr1_e_free e_init h_na n,
  end,
  begin -- k + 1 :
    have succ : n + k_n.succ = n + k_n + 1, by refl, rw succ,
    exact lt_trans (aux_decr1_e_free e_init h_na (n + k_n + 1)) k_ih,
  end,
end

lemma compl_lt_compl_iff_lt {B : Type*} {x y : B} [boolean_algebra B] :
yᶜ < xᶜ ↔ x < y :=
begin
  have h_ne_iff_ne : yᶜ ≠ xᶜ ↔ x ≠ y,  
  begin
    rw contra_pose_p', push_neg, rw compl_inj_iff, rw eq_comm,
  end,
  rw lt_iff_le_and_ne, rw lt_iff_le_and_ne,
  split,
  begin -- → 
    intros h, cases h with h_le h_ne,
    rw ← h_ne_iff_ne, rw ← compl_le_compl_iff_le,
    split, assumption, assumption,
  end,
  begin -- ←  
    intros h, cases h with h_le h_ne,
    rw h_ne_iff_ne, rw ← compl_le_compl_iff_le, rw compl_compl, rw compl_compl,
    split, assumption, assumption,
  end,
end

lemma increasing_seq {B : Type*} [hB : boolean_algebra B] (e_init : B) 
(h_na : not_bot_no_atoms_le e_init ) : 
∀ (n1 n2 : ℕ), n1 < n2 → 
(aux_sequence e_init h_na n1).e_freeᶜ < (aux_sequence e_init h_na n2).e_freeᶜ :=
begin
  intros n1 n2 hn12,-- rw compl_le_compl_iff_le,
  rw compl_lt_compl_iff_lt,
  have ex_k : ∃ (k : ℕ), n1.succ + k = n2, by exact nat.le.dest hn12,
  cases ex_k with k h,
  have h1 : n1.succ + k = n1 + k + 1, by rw nat.succ_add,
  rw ← h, rw h1,
  exact aux_decr_k_e_free e_init h_na n1 k,
end

def infinite_sequence_of_no_atoms {B : Type*} [hB : boolean_algebra B] (e_init : B) 
(h_na : not_bot_no_atoms_le e_init ) : ℕ → B :=
λ  (n : ℕ), (aux_sequence e_init h_na n).e_freeᶜ 

lemma strict_mono_infinite_sequence {B : Type*} [hB : boolean_algebra B] (e_init : B) 
(h_na : not_bot_no_atoms_le e_init ) : strict_mono (infinite_sequence_of_no_atoms e_init h_na) :=
-- ∀ (n1 n2 : ℕ), n1 < n2 → (aux_sequence e_init h_na n1).e_freeᶜ < (aux_sequence e_init h_na n2).e_freeᶜ :=
begin
  intros n1 n2 hn12,-- rw compl_le_compl_iff_le,
  unfold infinite_sequence_of_no_atoms,
  rw compl_lt_compl_iff_lt,
  have ex_k : ∃ (k : ℕ), n1.succ + k = n2, by exact nat.le.dest hn12,
  cases ex_k with k h,
  have h1 : n1.succ + k = n1 + k + 1, by rw nat.succ_add,
  rw ← h, rw h1,
  exact aux_decr_k_e_free e_init h_na n1 k,
end

--------------------------------

-- In this section we prove:
-- If there does not exist a strictly increasing sequence of idempotents
-- then there exists a finite set of atoms with supremum equal to the top element.

theorem exists_fin_atomset_sup_top_of_not_strict_mono {B : Type*} [hB : boolean_algebra B] 
( no_inf_seq : ¬( ∃ (strict_mono_seq : ℕ → B), strict_mono strict_mono_seq ) ) :
∃ (s : finset B), (∀ e ∈ s, ⊥ ⋖ e) ∧ boolean_algebra_finset_sup s = (⊤ : B) := 
begin
  have no_inf_atomset :  ¬ ex_inf_atoms B ,
  begin
    by_contradiction,
    have h_contra : ∃ (strint_mono_seq : ℕ → B), strict_mono strint_mono_seq,
    begin
      use inc_atoms h,
      exact strict_mono_inc_atoms h,
    end,
    contradiction,
  end,
  unfold ex_inf_atoms at no_inf_atomset, push_neg at no_inf_atomset, 
  cases no_inf_atomset with fin_atomset h_dum,
  cases h_dum with h_atoms h_no_atoms_outside,
  -- Now we have a maximal finite set of atoms 
  unfold ex_atom_outside at h_no_atoms_outside,

  -- Does not work: pust_neg at h_no_atoms_outside,
  -- Instead we prove a helper lemma:
  have no_atoms_outside' : ∀  (e : B), e ∈ fin_atomset ∨ ¬ (⊥ ⋖ e),
  begin
    revert h_no_atoms_outside, contrapose, push_neg, intros h, exact h,
  end,
  -- Now we will show that the supremum of the finite set atoms is equal to the top:
  have sup_eq_top : boolean_algebra_finset_sup fin_atomset = ⊤,
  begin
    by_contradiction h_not_top, 
    -- Does not work: push_neg at h,
    have hh : boolean_algebra_finset_sup fin_atomset ≠  ⊤, by exact h_not_top,
    let lt_top := ne.lt_top hh, --boolean_algebra_finset_sup fin_atomset < ⊤ 
    let e_init := ( boolean_algebra_finset_sup fin_atomset)ᶜ,
    -- We will show that '⊥ < e_init' and there are no atoms below e_init 
    have nb_lt : not_bot_no_atoms_le e_init,
    begin
      unfold not_bot_no_atoms_le,
      split,
      begin -- goal : ⊥ < e_init
        rw ← compl_top,
        exact compl_lt_compl_iff_lt.2 lt_top,
      end,
      begin -- goal: ∀ (e' : B), ⊥ < e' → e' ≤ e_init → ¬⊥ ⋖ e'
        intros e' hnb,
        contrapose,
        push_neg,
        intros e'_atom,
        let no_atoms_outside'' := no_atoms_outside' e',
        rw ← imp_iff_or_not at no_atoms_outside'',
        let e'_in_fin_atomset := no_atoms_outside'' e'_atom, -- e' ∈ fin_atomset
        let e'_lt_sup := (members_lt_sup fin_atomset e' h_atoms e'_atom ) e'_in_fin_atomset  e' e'_in_fin_atomset,
        by_contradiction h_lt_e_init,
        let e'le_inf_compl := le_inf e'_lt_sup h_lt_e_init,
        rw inf_compl_self at e'le_inf_compl,
        rw ← eq_bot_iff at e'le_inf_compl,
        rw e'le_inf_compl at e'_atom,
        cases e'_atom,
        let absurd := (ne_of_lt e'_atom_left), -- ⊥ ≠ ⊥
        contradiction,
      end,
    end,
    -- Now we get a contradiction by constructing a strictly increasing sequence of atoms
    have h_contra : ∃ (strint_mono_seq : ℕ → B), strict_mono strint_mono_seq,
    begin
      use (infinite_sequence_of_no_atoms e_init nb_lt),
      exact strict_mono_infinite_sequence e_init nb_lt,
    end,
    contradiction,
  end,
  use fin_atomset, exact and.intro h_atoms sup_eq_top,
end

