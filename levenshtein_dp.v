From Stdlib Require Import Ascii List ZArith Lia.
From compcert Require Import Integers.
From levenshtein_vst Require Import verif_levenshtein.

Import ListNotations.

Definition ascii_to_Z (c : ascii) : Z :=
  Z.of_nat (nat_of_ascii c).

Definition lev_dp_ascii (a_chars b_chars : list ascii) : Z :=
  lev_dp (map ascii_to_Z a_chars) (map ascii_to_Z b_chars).

Definition lev_dp_list (a_chars b_chars : list ascii) : nat :=
  Z.to_nat (lev_dp_ascii a_chars b_chars).

Definition outer_result_run (a_chars b_chars : list Z) (init : list Z) : Z :=
  outer_result a_chars b_chars init (length b_chars).

Lemma outer_result_run_eq :
  forall a_chars b_chars init,
    outer_result_run a_chars b_chars init =
    outer_result a_chars b_chars init (length b_chars).
Proof.
  intros. reflexivity.
Qed.

Lemma ascii_to_Z_byte_to_ascii :
  forall b, ascii_to_Z (byte_to_ascii b) = Byte.unsigned b.
Proof.
  intros b.
  unfold ascii_to_Z.
  apply byte_to_ascii_unsigned.
Qed.

Lemma lev_dp_ascii_of_bytes :
  forall a_bytes b_bytes,
    lev_dp_ascii (map byte_to_ascii a_bytes) (map byte_to_ascii b_bytes) =
    lev_dp (bytes_to_Z a_bytes) (bytes_to_Z b_bytes).
Proof.
  intros a_bytes b_bytes.
  unfold lev_dp_ascii.
  assert (Ha :
    map ascii_to_Z (map byte_to_ascii a_bytes) = bytes_to_Z a_bytes).
  { induction a_bytes as [|x xs IH].
    - reflexivity.
    - simpl. rewrite ascii_to_Z_byte_to_ascii, IH. reflexivity. }
  assert (Hb :
    map ascii_to_Z (map byte_to_ascii b_bytes) = bytes_to_Z b_bytes).
  { induction b_bytes as [|x xs IH].
    - reflexivity.
    - simpl. rewrite ascii_to_Z_byte_to_ascii, IH. reflexivity. }
  now rewrite Ha, Hb.
Qed.

Lemma Z_of_nat_to_nat_max0 :
  forall z, Z.of_nat (Z.to_nat z) = Z.max 0 z.
Proof.
  intro z.
  apply ZifyInst.of_nat_to_nat_eq.
Qed.

Lemma lev_dp_list_spec :
  forall a_chars b_chars,
    Z.of_nat (lev_dp_list a_chars b_chars) =
    Z.max 0 (lev_dp_ascii a_chars b_chars).
Proof.
  intros a_chars b_chars.
  unfold lev_dp_list, lev_dp_ascii.
  apply Z_of_nat_to_nat_max0.
Qed.

Corollary lev_dp_list_of_bytes_spec :
  forall a_bytes b_bytes,
    Z.of_nat (lev_dp_list (map byte_to_ascii a_bytes) (map byte_to_ascii b_bytes)) =
    Z.max 0 (lev_dp (bytes_to_Z a_bytes) (bytes_to_Z b_bytes)).
Proof.
  intros a_bytes b_bytes.
  rewrite lev_dp_list_spec.
  rewrite lev_dp_ascii_of_bytes.
  reflexivity.
Qed.

(* ================================================================ *)
(*     BRIDGE TO CRANE: Z-LEVEL DP = NAT-LEVEL DP                  *)
(* ================================================================ *)
(* Proves the Z-level Wagner-Fischer model from verif_levenshtein
   computes the same value as the nat-level model from BridgeDP.
   Combined with BridgeDP.lev_dp_string_eq_levenshtein_computed,
   this closes the end-to-end chain:
     C code -> lev_dp (Z) -> lev_dp_list (nat) ->
     levenshtein_computed -> minimality. *)

Require BridgeDP.
Require Levenshtein.
From Stdlib Require Import String.
Local Notation length := Datatypes.length.

(* -- ascii_to_Z is injective, bridging Z.eqb and ascii_dec -- *)

Lemma ascii_to_Z_zero : ascii_to_Z Ascii.zero = 0%Z.
Proof. reflexivity. Qed.

Lemma ascii_to_Z_inj : forall x y, ascii_to_Z x = ascii_to_Z y -> x = y.
Proof.
  intros x y H. unfold ascii_to_Z in H.
  apply Nat2Z.inj in H.
  rewrite <- (ascii_nat_embedding x), <- (ascii_nat_embedding y).
  now rewrite H.
Qed.

Lemma ascii_eqb_Z : forall x y : ascii,
  (ascii_to_Z x =? ascii_to_Z y)%Z =
  if ascii_dec x y then true else false.
Proof.
  intros x y.
  destruct (ascii_dec x y) as [Heq | Hneq].
  - subst. apply Z.eqb_refl.
  - apply Z.eqb_neq. intro H. apply Hneq. exact (ascii_to_Z_inj _ _ H).
Qed.

(* -- dp_min correspondence -- *)

Lemma dp_min_Z_nat : forall r d bd : nat,
  dp_min (Z.of_nat r) (Z.of_nat d) (Z.of_nat bd) =
  Z.of_nat (BridgeDP.dp_min r d bd).
Proof.
  intros r d bd.
  rewrite dp_min_spec, BridgeDP.dp_min_spec.
  rewrite !Nat2Z.inj_min, !Nat2Z.inj_succ. lia.
Qed.

(* -- inner_loop correspondence -- *)

Lemma inner_loop_Z_nat :
  forall a_chars b_char old_cache dist res,
    inner_loop (map ascii_to_Z a_chars) (ascii_to_Z b_char)
               (map Z.of_nat old_cache) (Z.of_nat dist) (Z.of_nat res) =
    let '(nc, fd, fr) :=
      BridgeDP.inner_loop a_chars b_char old_cache dist res in
    (map Z.of_nat nc, Z.of_nat fd, Z.of_nat fr).
Proof.
  induction a_chars as [|a rest IH]; intros b_char old_cache dist res.
  - destruct old_cache; reflexivity.
  - destruct old_cache as [|c cs].
    + reflexivity.
    + simpl. rewrite ascii_eqb_Z.
      destruct (ascii_dec b_char a) as [Heq | Hneq].
      * rewrite dp_min_Z_nat, IH.
        destruct (BridgeDP.inner_loop rest b_char cs c
                   (BridgeDP.dp_min res c dist)) as [[rc fd] fr].
        reflexivity.
      * replace (Z.of_nat dist + 1)%Z with (Z.of_nat (S dist)) by lia.
        rewrite dp_min_Z_nat, IH.
        destruct (BridgeDP.inner_loop rest b_char cs c
                   (BridgeDP.dp_min res c (S dist))) as [[rc fd] fr].
        reflexivity.
Qed.

(* -- process_row correspondence -- *)

Lemma process_row_Z_nat :
  forall a_chars b_char old_cache bIdx,
    process_row (map ascii_to_Z a_chars) (ascii_to_Z b_char)
                (map Z.of_nat old_cache) (Z.of_nat bIdx) =
    let '(nc, fr) :=
      BridgeDP.process_row a_chars b_char old_cache bIdx in
    (map Z.of_nat nc, Z.of_nat fr).
Proof.
  intros. unfold process_row, BridgeDP.process_row.
  rewrite inner_loop_Z_nat.
  destruct (BridgeDP.inner_loop a_chars b_char old_cache bIdx bIdx)
    as [[nc fd] fr].
  reflexivity.
Qed.

(* -- outer_cache correspondence -- *)

Lemma outer_cache_Z_nat :
  forall a_chars b_chars init k,
    outer_cache (map ascii_to_Z a_chars) (map ascii_to_Z b_chars)
                (map Z.of_nat init) k =
    map Z.of_nat (BridgeDP.outer_cache a_chars b_chars init k).
Proof.
  intros a_chars b_chars init k.
  induction k as [|k' IH]; [reflexivity|].
  simpl. rewrite IH.
  rewrite <- ascii_to_Z_zero, map_nth.
  rewrite process_row_Z_nat.
  destruct (BridgeDP.process_row a_chars (nth k' b_chars Ascii.zero)
             (BridgeDP.outer_cache a_chars b_chars init k') k')
    as [nc fr].
  reflexivity.
Qed.

(* -- outer_result correspondence -- *)

Lemma outer_result_Z_nat :
  forall a_chars b_chars init k,
    outer_result (map ascii_to_Z a_chars) (map ascii_to_Z b_chars)
                 (map Z.of_nat init) k =
    Z.of_nat (BridgeDP.outer_result a_chars b_chars init k).
Proof.
  intros a_chars b_chars init k.
  destruct k as [|k']; [reflexivity|].
  simpl. rewrite outer_cache_Z_nat.
  rewrite <- ascii_to_Z_zero, map_nth.
  rewrite process_row_Z_nat.
  destruct (BridgeDP.process_row a_chars (nth k' b_chars Ascii.zero)
             (BridgeDP.outer_cache a_chars b_chars init k') k')
    as [nc fr].
  reflexivity.
Qed.

(* -- init_cache correspondence -- *)

Lemma init_cache_Z_nat :
  forall la : nat,
    init_cache (Z.of_nat la) = map Z.of_nat (BridgeDP.init_cache la).
Proof.
  intros la. unfold init_cache, BridgeDP.init_cache.
  rewrite Nat2Z.id, map_map.
  apply map_ext_in. intros n _. lia.
Qed.

(* -- skipn helpers -- *)

Lemma skipn_hd_nth :
  forall {A : Type} k (l : list A) x rest (d : A),
    skipn k l = x :: rest -> nth k l d = x.
Proof.
  intros A k l. revert k.
  induction l as [|a l' IH]; intros k x rest d Hs.
  - destruct k; discriminate.
  - destruct k as [|k']; simpl in *.
    + inversion Hs. reflexivity.
    + exact (IH k' x rest d Hs).
Qed.

Lemma skipn_tl :
  forall {A : Type} k (l : list A) x rest,
    skipn k l = x :: rest -> skipn (S k) l = rest.
Proof.
  intros A k l. revert k.
  induction l as [|a l' IH]; intros k x rest Hs.
  - destruct k; discriminate.
  - destruct k as [|k']; simpl in *.
    + inversion Hs. reflexivity.
    + exact (IH k' x rest Hs).
Qed.

Lemma skipn_length_eq :
  forall {A : Type} k (l : list A),
    length (skipn k l) = length l - k.
Proof.
  intros A k l. revert k.
  induction l as [|a l' IH]; intros k.
  - destruct k; reflexivity.
  - destruct k as [|k']; simpl; [reflexivity | apply IH].
Qed.

(* -- outer_result_run = outer_result (BridgeDP/nat side) -- *)

Lemma outer_result_run_eq_gen :
  forall b_rem a b_all init k,
    a <> [] ->
    b_rem <> [] ->
    b_rem = skipn k b_all ->
    BridgeDP.outer_result_run a b_rem
      (BridgeDP.outer_cache a b_all init k) k =
    BridgeDP.outer_result a b_all init (length b_all).
Proof.
  induction b_rem as [|x rest IH]; intros a b_all init k Ha Hne Hskip.
  - contradiction.
  - destruct rest as [|y rest'].
    + (* Single element remaining: k is the last index. *)
      simpl.
      destruct (BridgeDP.process_row a x
                 (BridgeDP.outer_cache a b_all init k) k)
        as [nc fr] eqn:Hpr.
      assert (Hlen : length b_all = S k).
      { pose proof (skipn_length_eq k b_all) as Hsl.
        rewrite <- Hskip in Hsl. simpl in Hsl. lia. }
      rewrite Hlen. simpl.
      assert (Hnth : nth k b_all Ascii.zero = x).
      { exact (skipn_hd_nth k b_all x [] Ascii.zero (eq_sym Hskip)). }
      rewrite Hnth, Hpr. reflexivity.
    + (* Two or more remaining: recurse. *)
      simpl.
      destruct (BridgeDP.process_row a x
                 (BridgeDP.outer_cache a b_all init k) k)
        as [nc fr] eqn:Hpr.
      assert (Hnth : nth k b_all Ascii.zero = x).
      { exact (skipn_hd_nth k b_all x (y :: rest') Ascii.zero (eq_sym Hskip)). }
      assert (Hrest : y :: rest' = skipn (S k) b_all).
      { symmetry. exact (skipn_tl k b_all x (y :: rest') (eq_sym Hskip)). }
      assert (Hnc : nc = BridgeDP.outer_cache a b_all init (S k)).
      { unfold BridgeDP.outer_cache; fold BridgeDP.outer_cache.
        rewrite Hnth, Hpr. reflexivity. }
      rewrite Hnc.
      apply IH; [exact Ha | discriminate | exact Hrest].
Qed.

Corollary outer_result_run_eq_result :
  forall a b init,
    a <> [] ->
    b <> [] ->
    BridgeDP.outer_result_run a b init 0 =
    BridgeDP.outer_result a b init (length b).
Proof.
  intros a b init Ha Hb.
  exact (outer_result_run_eq_gen b a b init 0 Ha Hb eq_refl).
Qed.

(* -- Zlength helpers (defined in VST; reproved locally to avoid
       importing floyd.proofauto, which breaks nat scopes) -- *)

Local Lemma Zlength_aux_map : forall (A B : Type) (f : A -> B) (n : Z) (l : list A),
  Zlength_aux n B (map f l) = Zlength_aux n A l.
Proof.
  intros A B f n l. revert n.
  induction l as [|a l' IH]; intro n; simpl.
  - reflexivity.
  - apply IH.
Qed.

Local Lemma Zlength_map : forall (A B : Type) (f : A -> B) (l : list A),
  Zlength (map f l) = Zlength l.
Proof.
  intros. unfold Zlength. apply Zlength_aux_map.
Qed.

Local Lemma Zlength_aux_correct : forall (A : Type) (n : Z) (l : list A),
  Zlength_aux n A l = (n + Z.of_nat (Datatypes.length l))%Z.
Proof.
  intros A n l. revert n.
  induction l as [|a l' IH]; intro n; simpl.
  - lia.
  - rewrite IH. lia.
Qed.

Local Lemma Zlength_correct : forall (A : Type) (l : list A),
  Zlength l = Z.of_nat (Datatypes.length l).
Proof.
  intros. unfold Zlength. rewrite Zlength_aux_correct. lia.
Qed.

(* -- Main bridge theorem -- *)

Theorem lev_dp_eq_bridge :
  forall a b : list ascii,
    lev_dp (map ascii_to_Z a) (map ascii_to_Z b) =
    Z.of_nat (BridgeDP.lev_dp_list a b).
Proof.
  intros a b.
  unfold lev_dp, BridgeDP.lev_dp_list.
  rewrite !Zlength_map, !Zlength_correct.
  destruct a as [|a0 ar].
  - simpl. lia.
  - destruct b as [|b0 br].
    + simpl.
      replace (Z.of_nat (S (length ar)) =? 0)%Z with false
        by (symmetry; apply Z.eqb_neq; lia).
      simpl. lia.
    + simpl length.
      replace (Z.of_nat (S (length ar)) =? 0)%Z with false
        by (symmetry; apply Z.eqb_neq; lia).
      replace (Z.of_nat (S (length br)) =? 0)%Z with false
        by (symmetry; apply Z.eqb_neq; lia).
      rewrite Nat2Z.id, init_cache_Z_nat, outer_result_Z_nat.
      f_equal. symmetry.
      apply outer_result_run_eq_result; discriminate.
Qed.

(* -- End-to-end corollary -- *)

Corollary lev_dp_eq_levenshtein_computed :
  forall a b : list ascii,
    lev_dp (map ascii_to_Z a) (map ascii_to_Z b) =
    Z.of_nat (Levenshtein.levenshtein_computed
                (string_of_list_ascii a) (string_of_list_ascii b)).
Proof.
  intros a b.
  rewrite lev_dp_eq_bridge. f_equal.
  rewrite BridgeDP.lev_dp_list_rev_spec, BridgeDP.lev_spec_list_rev.
  reflexivity.
Qed.
