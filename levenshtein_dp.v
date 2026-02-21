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
