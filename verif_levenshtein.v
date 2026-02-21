(* verif_levenshtein.v *)
(* VST verification of the Levenshtein distance C implementation.
   Proves that levenshtein_n computes the Wagner-Fischer DP algorithm,
   which is then shown equivalent to the intrinsically-verified Rocq
   implementation from bloomberg/crane (PR #17). *)

From Stdlib Require Import String Ascii List ZArith Lia.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
From VST Require Import floyd.proofauto floyd.library.
Require Import levenshtein_vst.levenshtein.

Import ListNotations.

(* ================================================================ *)
(*                     VST BOILERPLATE                               *)
(* ================================================================ *)

#[export] Instance CompSpecs : compspecs.
  make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.
#[export] Existing Instance NullExtension.Espec.

(* ================================================================ *)
(*                     FUNCTIONAL MODEL                              *)
(* ================================================================ *)
(* A pure Coq model of the Wagner-Fischer DP algorithm matching the  *)
(* C code's structure. All arithmetic is over Z (unbounded integers).*)
(* The bridge to CompCert's machine integers is handled in the       *)
(* funspec and proof, not here.                                      *)

(** The min-of-three computation from the C code's nested if-else.
    Equivalent to: min(result + 1, distance + 1, bDistance).
    Here [result] = left, [distance] = above (old cache), [bDistance] =
    diagonal (with +1 for mismatch). *)
Definition dp_min (result distance bDistance : Z) : Z :=
  if (distance >? result)%Z then
    if (bDistance >? result)%Z then result + 1 else bDistance
  else
    if (bDistance >? distance)%Z then distance + 1 else bDistance.

(** The full inner loop: for each index i in 0..length-1, compute
    the new cache value using the DP recurrence.
    Parameters:
    - [a_chars]: characters of string a (as unsigned byte values)
    - [b_char]: current character of string b (unsigned byte value)
    - [old_cache]: cache from the previous row
    - [distance]: diagonal value (initially bIndex)
    - [result]: left value (initially bIndex)
    Returns: (new_cache, final_distance, final_result). *)
Fixpoint inner_loop (a_chars : list Z) (b_char : Z) (old_cache : list Z)
    (distance result : Z) : list Z * Z * Z :=
  match a_chars, old_cache with
  | a_i :: a_rest, c_i :: c_rest =>
    let bDistance := if (b_char =? a_i)%Z then distance else distance + 1 in
    let new_result := dp_min result c_i bDistance in
    let '(rest_cache, fd, fr) :=
        inner_loop a_rest b_char c_rest c_i new_result in
    (new_result :: rest_cache, fd, fr)
  | _, _ => ([], distance, result)
  end.

(** Partial inner loop: process only the first [n] elements.
    Used to express the inner loop invariant. *)
Fixpoint inner_loop_n (a_chars : list Z) (b_char : Z) (old_cache : list Z)
    (distance result : Z) (n : nat) : list Z * Z * Z :=
  match n with
  | O => ([], distance, result)
  | S n' =>
    match a_chars, old_cache with
    | a_i :: a_rest, c_i :: c_rest =>
      let bDistance := if (b_char =? a_i)%Z then distance else distance + 1 in
      let new_result := dp_min result c_i bDistance in
      let '(rest_cache, fd, fr) :=
          inner_loop_n a_rest b_char c_rest c_i new_result n' in
      (new_result :: rest_cache, fd, fr)
    | _, _ => ([], distance, result)
    end
  end.

(** Process one row of the DP table (one outer loop iteration).
    Returns (new_cache, row_result). *)
Definition process_row (a_chars : list Z) (b_char : Z)
    (old_cache : list Z) (bIndex : Z) : list Z * Z :=
  let '(new_cache, _, final_result) :=
      inner_loop a_chars b_char old_cache bIndex bIndex in
  (new_cache, final_result).

(** Cache state after processing rows 0..k-1.
    Used in the outer loop invariant. *)
Fixpoint outer_cache (a_chars b_chars : list Z) (init : list Z)
    (k : nat) : list Z :=
  match k with
  | O => init
  | S k' =>
    let prev := outer_cache a_chars b_chars init k' in
    let b_j := nth k' b_chars 0 in
    fst (process_row a_chars b_j prev (Z.of_nat k'))
  end.

(** Result of the last processed row. *)
Definition outer_result (a_chars b_chars : list Z) (init : list Z)
    (k : nat) : Z :=
  match k with
  | O => 0
  | S k' =>
    let prev := outer_cache a_chars b_chars init k' in
    let b_j := nth k' b_chars 0 in
    snd (process_row a_chars b_j prev (Z.of_nat k'))
  end.

(** Initial cache: [1, 2, ..., la]. *)
Definition init_cache (la : Z) : list Z :=
  map (fun i => Z.of_nat i + 1) (seq 0 (Z.to_nat la)).

(** The complete functional model of the C algorithm. *)
Definition lev_dp (a_chars b_chars : list Z) : Z :=
  let la := Zlength a_chars in
  let lb := Zlength b_chars in
  if (la =? 0)%Z then lb
  else if (lb =? 0)%Z then la
  else outer_result a_chars b_chars (init_cache la) (Z.to_nat lb).

(* ================================================================ *)
(*                   MODEL PROPERTIES                                *)
(* ================================================================ *)

(** dp_min is indeed the minimum of three candidates. *)
Lemma dp_min_spec : forall r d bd,
  dp_min r d bd = Z.min (r + 1) (Z.min (d + 1) bd).
Proof.
  intros r d bd. unfold dp_min.
  destruct (d >? r) eqn:Hdr; destruct (bd >? r) eqn:Hbr;
    try destruct (bd >? d) eqn:Hbd;
    rewrite ?Z.gtb_ltb in *;
    destruct (Z.ltb_spec r d); destruct (Z.ltb_spec r bd);
      try destruct (Z.ltb_spec d bd);
      try lia.
Qed.

(** inner_loop and inner_loop_n agree when n = length of inputs. *)
Lemma inner_loop_n_full : forall a_chars b_char old_cache dist res,
  length a_chars = length old_cache ->
  inner_loop_n a_chars b_char old_cache dist res (length a_chars)
  = inner_loop a_chars b_char old_cache dist res.
Proof.
  intros a_chars.
  induction a_chars as [|a rest IH]; intros b_char old_cache dist res Hlen.
  - destruct old_cache; simpl in *; [reflexivity | lia].
  - destruct old_cache as [|c cs]; simpl in *; [lia |].
    injection Hlen as Hlen.
    rewrite IH by assumption.
    reflexivity.
Qed.

(** Base case of [inner_loop_n]: processing 0 elements. *)
Lemma inner_loop_n_zero : forall a_chars b_char old_cache dist res,
  inner_loop_n a_chars b_char old_cache dist res 0%nat = ((@nil Z), dist, res).
Proof.
  intros a_chars b_char old_cache dist res.
  destruct a_chars; reflexivity.
Qed.

(** init_cache has the right length. *)
Lemma init_cache_Zlength : forall la,
  0 <= la -> Zlength (init_cache la) = la.
Proof.
  intros la Hla. unfold init_cache.
  rewrite Zlength_map, Zlength_correct, length_seq.
  lia.
Qed.

(** nth of map when index is in bounds. *)
Lemma nth_map_seq_gen : forall (f : nat -> Z) start m n d,
  (n < m)%nat ->
  nth n (map f (seq start m)) d = f (start + n)%nat.
Proof.
  intros f start m. revert start.
  induction m as [|m' IH]; intros start n d Hn.
  - lia.
  - simpl. destruct n as [|n'].
    + f_equal. lia.
    + rewrite IH by lia. f_equal. lia.
Qed.

(** init_cache values. *)
Lemma init_cache_nth : forall la i,
  0 <= la -> (0 <= i < la)%Z ->
  nth (Z.to_nat i) (init_cache la) 0 = i + 1.
Proof.
  intros la i Hla Hi.
  unfold init_cache.
  rewrite nth_map_seq_gen by lia.
  simpl. lia.
Qed.

(* ================================================================ *)
(*                    FUNCTION SPECIFICATIONS                         *)
(* ================================================================ *)

(** Calloc spec: allocates an array of [n] unsigned longs.
    AXIOM: we assume calloc succeeds (returns non-NULL).
    The C code does not check for NULL after calloc, so it has
    undefined behavior if calloc fails. We axiomatize success. *)
Definition calloc_spec :=
  DECLARE _calloc
  WITH n : Z, gv : globals
  PRE [ tulong, tulong ]
    PROP (0 < n;
          n * sizeof tulong <= Ptrofs.max_unsigned)
    PARAMS (Vlong (Int64.repr n);
            Vlong (Int64.repr (sizeof tulong)))
    GLOBALS (gv)
    SEP (mem_mgr gv)
  POST [ tptr tvoid ]
    EX p : val,
    PROP ()
    RETURN (p)
    SEP (mem_mgr gv;
         malloc_token Ews (tarray tulong n) p;
         data_at_ Ews (tarray tulong n) p).

(** Helper: convert a list of bytes to a list of Z (unsigned values). *)
Definition bytes_to_Z (bs : list byte) : list Z :=
  map Byte.unsigned bs.

Definition byte_to_ascii (b : byte) : ascii :=
  ascii_of_nat (Z.to_nat (Byte.unsigned b)).

Lemma byte_to_ascii_unsigned :
  forall b, Z.of_nat (nat_of_ascii (byte_to_ascii b)) = Byte.unsigned b.
Proof.
  intros b.
  unfold byte_to_ascii.
  pose proof (Byte.unsigned_range b) as Hr.
  change Byte.modulus with 256 in Hr.
  assert (Hlt_nat : (Z.to_nat (Byte.unsigned b) < 256)%nat).
  { pose proof (Z2Nat.inj_lt (Byte.unsigned b) 256) as Hiff.
    assert (H256 : 0 <= 256) by lia.
    specialize (Hiff (proj1 Hr) H256).
    apply (proj1 Hiff).
    lia. }
  rewrite nat_ascii_embedding by exact Hlt_nat.
  rewrite Z2Nat.id by lia.
  lia.
Qed.

Lemma byte_to_ascii_eq_iff :
  forall b1 b2,
    ((Byte.unsigned b1 =? Byte.unsigned b2)%Z = true <->
     byte_to_ascii b1 = byte_to_ascii b2).
Proof.
  intros b1 b2. split.
  - intros H.
    apply Z.eqb_eq in H.
    unfold byte_to_ascii.
    now rewrite H.
  - intros H.
    apply (f_equal (fun a => Z.of_nat (nat_of_ascii a))) in H.
    rewrite !byte_to_ascii_unsigned in H.
    now apply Z.eqb_eq.
Qed.

(** Helper: convert cache (list Z) to val list for data_at. *)
Definition cache_to_val (cache : list Z) : list val :=
  map (fun x => Vlong (Int64.repr x)) cache.

(** Levenshtein distance specification.
    Given readable arrays [a] and [b] of characters with lengths
    [la] and [lb], returns the Levenshtein distance as computed
    by the Wagner-Fischer DP algorithm. *)
Definition levenshtein_n_spec :=
  DECLARE _levenshtein_n
  WITH sh_a : share, sh_b : share,
       a_ptr : val, b_ptr : val,
       a_contents : list byte, b_contents : list byte,
       la : Z, lb : Z,
       gv : globals
  PRE [ tptr tschar, tulong, tptr tschar, tulong ]
    PROP (readable_share sh_a;
          readable_share sh_b;
          Zlength a_contents = la;
          Zlength b_contents = lb;
          0 <= la <= Int64.max_unsigned;
          0 <= lb <= Int64.max_unsigned;
          la + lb <= Int64.max_unsigned;
          0 < la -> la * sizeof tulong <= Ptrofs.max_unsigned)
    PARAMS (a_ptr; Vlong (Int64.repr la);
            b_ptr; Vlong (Int64.repr lb))
    GLOBALS (gv)
    SEP (mem_mgr gv;
         data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
         data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr)
  POST [ tulong ]
    PROP ()
    RETURN (Vlong (Int64.repr
              (lev_dp (bytes_to_Z a_contents) (bytes_to_Z b_contents))))
    SEP (mem_mgr gv;
         data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
         data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr).

(** Gprog: all function specs for the program.
    [with_library prog] adds specs for builtins and [free]. *)
Definition Gprog : funspecs :=
  ltac:(with_library prog [calloc_spec; levenshtein_n_spec]).

(* ================================================================ *)
(*                    LOOP INVARIANTS                                 *)
(* ================================================================ *)

(** Abbreviations for readability. *)
Definition a_Z (a_contents : list byte) := bytes_to_Z a_contents.
Definition b_Z (b_contents : list byte) := bytes_to_Z b_contents.

(** Init loop invariant:
    After processing indices 0..i-1, cache contains [1, 2, ..., i]
    followed by uninitialized values. *)
Definition init_loop_inv
    (sh_a sh_b : share)
    (a_ptr b_ptr cache_ptr : val)
    (a_contents b_contents : list byte)
    (la lb : Z) (gv : globals) :=
  EX i : Z,
  PROP (0 <= i <= la)
  LOCAL (temp _index (Vlong (Int64.repr i));
         temp _result (Vlong (Int64.repr 0));
         temp _cache cache_ptr;
         temp _length (Vlong (Int64.repr la));
         temp _bLength (Vlong (Int64.repr lb));
         temp _a a_ptr;
         temp _b b_ptr;
         gvars gv)
  SEP (mem_mgr gv;
       malloc_token Ews (tarray tulong la) cache_ptr;
       data_at Ews (tarray tulong la)
         (cache_to_val (firstn (Z.to_nat i) (init_cache la))
          ++ Zrepeat Vundef (la - i))
         cache_ptr;
       data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
       data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr).

(** Outer loop invariant:
    After processing rows 0..k-1 of the DP table, the cache holds
    the k-th row and bIndex = k. *)
Definition outer_loop_inv
    (sh_a sh_b : share)
    (a_ptr b_ptr cache_ptr : val)
    (a_contents b_contents : list byte)
    (la lb : Z) (gv : globals) :=
  EX k : Z, EX res_v : val,
  PROP (0 <= k <= lb;
        res_v = Vlong (Int64.repr
          (outer_result (a_Z a_contents) (b_Z b_contents)
                        (init_cache la) (Z.to_nat k))))
  LOCAL (temp _bIndex (Vlong (Int64.repr k));
         temp _result res_v;
         temp _cache cache_ptr;
         temp _length (Vlong (Int64.repr la));
         temp _bLength (Vlong (Int64.repr lb));
         temp _a a_ptr;
         temp _b b_ptr;
         gvars gv)
  SEP (mem_mgr gv;
       malloc_token Ews (tarray tulong la) cache_ptr;
       data_at Ews (tarray tulong la)
         (cache_to_val
            (outer_cache (a_Z a_contents) (b_Z b_contents)
                         (init_cache la) (Z.to_nat k)))
         cache_ptr;
       data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
       data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr).

(** Inner loop invariant:
    After processing indices 0..idx-1 within row [bIdx], the first
    [idx] cache entries have been updated, the rest are from the
    previous row. The [distance] and [result] variables track the
    DP state. *)
Definition inner_loop_inv
    (sh_a sh_b : share)
    (a_ptr b_ptr cache_ptr : val)
    (a_contents b_contents : list byte)
    (la lb bIdx : Z)
    (old_cache : list Z) (b_char : Z) (gv : globals) :=
  EX idx : Z, EX dist : Z, EX res : Z,
  PROP (0 <= idx <= la;
        Zlength old_cache = la;
        let '(prefix, d, r) :=
          inner_loop_n (a_Z a_contents) b_char old_cache bIdx bIdx
                       (Z.to_nat idx) in
        dist = d /\ res = r /\
        Zlength prefix = idx)
  LOCAL (temp _index (Vlong (Int64.repr idx));
         temp _distance (Vlong (Int64.repr dist));
         temp _result (Vlong (Int64.repr res));
         temp _code
           (Vint (Int.repr (Byte.signed (Byte.repr b_char))));
         temp _bIndex (Vlong (Int64.repr (bIdx + 1)));
         temp _cache cache_ptr;
         temp _length (Vlong (Int64.repr la));
         temp _bLength (Vlong (Int64.repr lb));
         temp _a a_ptr;
         temp _b b_ptr;
         gvars gv)
  SEP (mem_mgr gv;
       malloc_token Ews (tarray tulong la) cache_ptr;
       data_at Ews (tarray tulong la)
         (let '(prefix, _, _) :=
            inner_loop_n (a_Z a_contents) b_char old_cache bIdx bIdx
                         (Z.to_nat idx) in
          cache_to_val prefix
          ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
         cache_ptr;
       data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
       data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr).

(* ================================================================ *)
(*                 HELPER LEMMAS FOR PROOF                           *)
(* ================================================================ *)

(** Byte equality: comparing signed char representations in CompCert
    agrees with comparing unsigned byte values. *)
Lemma byte_signed_in_int_range : forall b : byte,
  Int.min_signed <= Byte.signed b <= Int.max_signed.
Proof.
  intros b.
  pose proof (Byte.signed_range b).
  change Byte.min_signed with (-128) in H.
  change Byte.max_signed with 127 in H.
  rep_lia.
Qed.

Lemma byte_eq_unsigned : forall b1 b2 : byte,
  Int.eq (Int.repr (Byte.signed b1)) (Int.repr (Byte.signed b2)) =
  (Byte.unsigned b1 =? Byte.unsigned b2)%Z.
Proof.
  intros b1 b2.
  destruct (Z.eqb_spec (Byte.unsigned b1) (Byte.unsigned b2)) as [Heq | Hneq].
  - assert (b1 = b2).
    { rewrite <- (Byte.repr_unsigned b1), <- (Byte.repr_unsigned b2).
      f_equal. exact Heq. }
    subst. rewrite Int.eq_true. reflexivity.
  - rewrite Int.eq_false; [reflexivity |].
    intro Hcontra.
    apply Hneq.
    assert (Hs : Byte.signed b1 = Byte.signed b2).
    { pose proof (byte_signed_in_int_range b1).
      pose proof (byte_signed_in_int_range b2).
      rewrite <- (Int.signed_repr (Byte.signed b1)) by lia.
      rewrite <- (Int.signed_repr (Byte.signed b2)) by lia.
      f_equal. exact Hcontra. }
    apply (f_equal Byte.repr) in Hs.
    rewrite !Byte.repr_signed in Hs.
    apply (f_equal Byte.unsigned) in Hs.
    exact Hs.
Qed.

(** Zlength of cache_to_val. *)
Lemma cache_to_val_Zlength : forall cache,
  Zlength (cache_to_val cache) = Zlength cache.
Proof.
  intros. unfold cache_to_val.
  rewrite Zlength_map. reflexivity.
Qed.

(** cache_to_val distributes over app. *)
Lemma cache_to_val_app : forall l1 l2,
  cache_to_val (l1 ++ l2) = cache_to_val l1 ++ cache_to_val l2.
Proof.
  intros. unfold cache_to_val. rewrite map_app. reflexivity.
Qed.

(** Current element at position [idx] in [prefix ++ skipn idx old_cache],
    after mapping through [cache_to_val], is the mapped [old_cache[idx]]. *)
Lemma cache_current_Znth : forall prefix old_cache idx,
  Zlength prefix = idx ->
  0 <= idx < Zlength old_cache ->
  Znth idx
    (cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
  = Vlong (Int64.repr (Znth idx old_cache)).
Proof.
  intros prefix old_cache idx Hprefix Hidx.
  rewrite Znth_app2.
  2:{ rewrite cache_to_val_Zlength, Hprefix. lia. }
  replace (idx - Zlength (cache_to_val prefix)) with 0.
  2:{ rewrite cache_to_val_Zlength, Hprefix. lia. }
  unfold cache_to_val.
  rewrite Znth_map.
  2:{
    rewrite Zlength_skipn.
    rewrite Z.max_r by lia.
    rewrite Z.max_r by lia.
    split; lia.
  }
  rewrite Znth_skipn by lia.
  replace (0 + idx) with idx by lia.
  reflexivity.
Qed.

(** inner_loop output has the same length as input. *)
Lemma inner_loop_length : forall a_chars b_char old_cache dist res,
  length a_chars = length old_cache ->
  length (fst (fst (inner_loop a_chars b_char old_cache dist res))) = length old_cache.
Proof.
  induction a_chars as [|a rest IH]; intros b_char old_cache dist res Hlen.
  - destruct old_cache; simpl in *; [reflexivity | lia].
  - destruct old_cache as [|c cs]; simpl in *; [lia |].
    injection Hlen as Hlen.
    set (bd := if (b_char =? a)%Z then dist else dist + 1).
    destruct (inner_loop rest b_char cs c (dp_min res c bd)) as [[rc fd] fr] eqn:Heq.
    simpl. f_equal.
    specialize (IH b_char cs c (dp_min res c bd) Hlen).
    rewrite Heq in IH. simpl in IH. exact IH.
Qed.

(** process_row preserves length. *)
Lemma process_row_length : forall a_chars b_char old_cache bIdx,
  length a_chars = length old_cache ->
  length (fst (process_row a_chars b_char old_cache bIdx)) = length old_cache.
Proof.
  intros. unfold process_row.
  destruct (inner_loop a_chars b_char old_cache bIdx bIdx) as [[nc fd] fr] eqn:Heq.
  simpl.
  pose proof (inner_loop_length a_chars b_char old_cache bIdx bIdx H).
  rewrite Heq in H0. simpl in H0. exact H0.
Qed.

(** outer_cache preserves length (nat). *)
Lemma outer_cache_length_nat : forall a_chars b_chars init k,
  (forall k', (k' < k)%nat ->
    length a_chars = length (outer_cache a_chars b_chars init k')) ->
  length (outer_cache a_chars b_chars init k) = length init.
Proof.
  intros a_chars b_chars init k.
  induction k as [|k' IH]; intros Hprev; simpl.
  - reflexivity.
  - rewrite process_row_length with (old_cache := outer_cache a_chars b_chars init k').
    + apply IH. intros k'' Hk''. apply Hprev. lia.
    + apply Hprev. lia.
Qed.

(** outer_cache preserves Zlength. *)
Lemma outer_cache_length : forall a_chars b_chars init k,
  length a_chars = length init ->
  Zlength (outer_cache a_chars b_chars init k) = Zlength init.
Proof.
  intros a_chars b_chars init k Hinit.
  rewrite !Zlength_correct.
  f_equal.
  induction k as [|k' IH]; simpl.
  - reflexivity.
  - rewrite process_row_length with (old_cache := outer_cache a_chars b_chars init k').
    + exact IH.
    + rewrite IH. exact Hinit.
Qed.

(** If [n < length l], [firstn (S n) l] is [firstn n l] plus the nth element. *)
Lemma firstn_snoc_nth {A} (l : list A) (n : nat) (d : A) :
  (n < length l)%nat ->
  firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  revert l.
  induction n as [|n IH]; intros l Hlt.
  - destruct l as [|x xs]; [inversion Hlt|]. simpl. reflexivity.
  - destruct l as [|x xs]; [inversion Hlt|]. simpl in *. f_equal.
    apply IH. lia.
Qed.

(** Prefix extension property for [init_cache] after [cache_to_val]. *)
Lemma init_cache_prefix_snoc : forall la i,
  0 <= la -> 0 <= i < la ->
  cache_to_val (firstn (Z.to_nat (i + 1)) (init_cache la)) =
  cache_to_val (firstn (Z.to_nat i) (init_cache la)) ++ [Vlong (Int64.repr (i + 1))].
Proof.
  intros la i Hla Hi.
  unfold cache_to_val.
  replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)).
  2:{ rewrite Z2Nat.inj_add by lia. simpl. lia. }
  rewrite (firstn_snoc_nth (init_cache la) (Z.to_nat i) 0).
  - rewrite map_app. simpl.
    f_equal.
    rewrite init_cache_nth; try lia.
    reflexivity.
  - unfold init_cache.
    rewrite length_map, length_seq.
    apply Z2Nat.inj_lt; lia.
Qed.

(** One init-loop write step transforms cache from index [i] to [i+1]. *)
Lemma init_loop_cache_update : forall la i,
  0 <= la -> 0 <= i < la ->
  upd_Znth i
    (cache_to_val (firstn (Z.to_nat i) (init_cache la)) ++ Zrepeat Vundef (la - i))
    (Vlong (Int64.repr (i + 1)))
  = cache_to_val (firstn (Z.to_nat (i + 1)) (init_cache la)) ++ Zrepeat Vundef (la - (i + 1)).
Proof.
  intros la i Hla Hi.
  unfold Zrepeat.
  assert (Hzlen : Zlength (cache_to_val (firstn (Z.to_nat i) (init_cache la))) = i).
  { unfold cache_to_val.
    rewrite Zlength_map.
    rewrite Zlength_firstn.
    rewrite init_cache_Zlength by lia.
    rewrite Z.max_r by lia.
    rewrite Z.min_l; lia. }
  rewrite (upd_init
             (cache_to_val (firstn (Z.to_nat i) (init_cache la)))
             i la Vundef (Vlong (Int64.repr (i + 1)))); try lia.
  rewrite init_cache_prefix_snoc by lia.
  rewrite <- app_assoc. simpl. reflexivity.
Qed.

(** One-step expansion of [inner_loop_n] at successor index (nat form). *)
Lemma inner_loop_n_step_gen :
  forall a_chars b_char old_cache dist res n,
    length a_chars = length old_cache ->
    (n < length a_chars)%nat ->
    let '(prefix, d, r) := inner_loop_n a_chars b_char old_cache dist res n in
    inner_loop_n a_chars b_char old_cache dist res (S n) =
      let a_i := nth n a_chars 0 in
      let c_i := nth n old_cache 0 in
      let bDistance := if b_char =? a_i then d else d + 1 in
      let new_result := dp_min r c_i bDistance in
      (prefix ++ [new_result], c_i, new_result).
Proof.
  intros a_chars b_char old_cache dist res n.
  revert a_chars old_cache dist res.
  induction n as [|n IH]; intros a_chars old_cache dist res Hlen Hn.
  - destruct a_chars as [|a0 ar]; [inversion Hn|].
    destruct old_cache as [|c0 cr]; [inversion Hlen|].
    simpl.
    rewrite inner_loop_n_zero.
    reflexivity.
  - destruct a_chars as [|a0 ar]; [inversion Hn|].
    destruct old_cache as [|c0 cr]; [inversion Hlen|].
    simpl in Hlen. inversion Hlen; subst.
    simpl in Hn.
    simpl.
    set (bd := if (b_char =? a0)%Z then dist else dist + 1).
    set (nr := dp_min res c0 bd).
    assert (Hlen' : length ar = length cr) by lia.
    assert (Hn' : (n < length ar)%nat) by lia.
    specialize (IH ar cr c0 nr Hlen' Hn').
    simpl in IH.
    destruct (inner_loop_n ar b_char cr c0 nr n) as [[prefix d] r] eqn:Hi.
    simpl in IH.
    simpl.
    rewrite IH.
    reflexivity.
Qed.

(** One-step expansion of [inner_loop_n] at successor index (Z form). *)
Lemma inner_loop_n_step_Z :
  forall a_chars b_char old_cache dist res idx,
    Zlength a_chars = Zlength old_cache ->
    0 <= idx < Zlength a_chars ->
    let '(prefix, d, r) :=
      inner_loop_n a_chars b_char old_cache dist res (Z.to_nat idx) in
    inner_loop_n a_chars b_char old_cache dist res (Z.to_nat (idx + 1)) =
      let a_i := Znth idx a_chars in
      let c_i := Znth idx old_cache in
      let bDistance := if b_char =? a_i then d else d + 1 in
      let new_result := dp_min r c_i bDistance in
      (prefix ++ [new_result], c_i, new_result).
Proof.
  intros a_chars b_char old_cache dist res idx Hlenz Hidx.
  destruct Hidx as [Hidx0 Hidxlt].
  rewrite !Zlength_correct in Hlenz.
  assert (Hlen : length a_chars = length old_cache) by lia.
  assert (Hnlt : (Z.to_nat idx < length a_chars)%nat).
  {
    pose proof (Z2Nat.inj_lt idx (Z.of_nat (length a_chars))
                  Hidx0 (Nat2Z.is_nonneg (length a_chars))) as Hconv.
    replace (length a_chars) with (Z.to_nat (Z.of_nat (length a_chars)))
      by apply Nat2Z.id.
    apply (proj1 Hconv).
    rewrite Zlength_correct in Hidxlt.
    lia.
  }
  rewrite Z2Nat.inj_add by lia.
  simpl.
  rewrite Nat.add_1_r.
  remember (inner_loop_n a_chars b_char old_cache dist res (Z.to_nat idx))
    as t eqn:Ht.
  destruct t as [[prefix d] r].
  simpl.
  pose proof (inner_loop_n_step_gen a_chars b_char old_cache dist res
                (Z.to_nat idx) Hlen Hnlt) as Hstep.
  rewrite <- Ht in Hstep.
  simpl in Hstep.
  rewrite Hstep.
  assert (Hidx_old : 0 <= idx < Zlength old_cache).
  {
    split; [lia|].
    rewrite !Zlength_correct.
    rewrite <- Hlen.
    rewrite Zlength_correct in Hidxlt.
    exact Hidxlt.
  }
  rewrite (nth_Znth idx a_chars); [|split; lia].
  rewrite (nth_Znth idx old_cache); [|exact Hidx_old].
  replace (Z.of_nat (Z.to_nat idx)) with idx by lia.
  reflexivity.
Qed.

(** Updating cache at [idx] appends one DP value to the computed prefix. *)
Lemma cache_update_step :
  forall prefix old_cache idx new_res,
    Zlength prefix = idx ->
    0 <= idx < Zlength old_cache ->
    upd_Znth idx
      (cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
      (Vlong (Int64.repr new_res)) =
    cache_to_val (prefix ++ [new_res]) ++
      cache_to_val (skipn (Z.to_nat (idx + 1)) old_cache).
Proof.
  intros prefix old_cache idx new_res Hprefix Hidx.
  destruct Hidx as [Hidx0 Hidxlt].
  rewrite upd_Znth_app2.
  2:{
    rewrite cache_to_val_Zlength, Hprefix.
    rewrite cache_to_val_Zlength, Zlength_skipn.
    rewrite Z.max_r by lia.
    split; lia.
  }
  rewrite cache_to_val_Zlength, Hprefix.
  replace (idx - idx) with 0 by lia.
  assert (Hlt_nat : (Z.to_nat idx < length old_cache)%nat).
  {
    pose proof (Z2Nat.inj_lt idx (Z.of_nat (length old_cache))
                  Hidx0 (Nat2Z.is_nonneg (length old_cache))) as Hconv.
    replace (length old_cache) with (Z.to_nat (Z.of_nat (length old_cache)))
      by apply Nat2Z.id.
    apply (proj1 Hconv).
    rewrite Zlength_correct in Hidxlt.
    lia.
  }
  assert (Hskip :
    skipn (Z.to_nat idx) old_cache =
      Znth (Z.of_nat (Z.to_nat idx)) old_cache :: skipn (S (Z.to_nat idx)) old_cache).
  {
    apply skipn_cons.
    exact Hlt_nat.
  }
  rewrite Z2Nat.id in Hskip by lia.
  rewrite Hskip.
  unfold cache_to_val.
  simpl.
  rewrite upd_Znth0.
  rewrite cache_to_val_app.
  simpl.
  replace (Z.to_nat (idx + 1)) with (S (Z.to_nat idx)) by lia.
  replace (skipn (S (Z.to_nat idx)) old_cache) with
      (match old_cache with
       | [] => []
       | _ :: l => skipn (Z.to_nat idx) l
       end).
  2:{ destruct old_cache; reflexivity. }
  unfold cache_to_val.
  rewrite <- app_assoc.
  simpl.
  reflexivity.
Qed.

(** Bounds for [init_cache]. *)
Lemma init_cache_bounds :
  forall la,
    0 <= la ->
    Forall (fun x => 0 <= x <= la) (init_cache la).
Proof.
  intros la Hla.
  unfold init_cache.
  apply Forall_forall.
  intros x HIn.
  apply in_map_iff in HIn.
  destruct HIn as [n [Hx Hn]].
  subst x.
  apply in_seq in Hn.
  destruct Hn as [Hn0 Hnlt].
  split; lia.
Qed.

(** Bounds for the diagonal candidate used in the DP recurrence. *)
Lemma bDistance_bounds :
  forall b_char a dist B,
    0 <= dist <= B ->
    0 <= (if (b_char =? a)%Z then dist else dist + 1) <= B + 1.
Proof.
  intros b_char a dist B Hdist.
  destruct (b_char =? a)%Z; lia.
Qed.

(** If inputs to [dp_min] are in range, so is its result. *)
Lemma dp_min_bounds :
  forall res c bd B,
    0 <= res <= B + 1 ->
    0 <= c <= B ->
    0 <= bd <= B + 1 ->
    0 <= dp_min res c bd <= B + 1.
Proof.
  intros res c bd B Hres Hc Hbd.
  rewrite dp_min_spec.
  split.
  - apply Z.min_glb.
    + lia.
    + apply Z.min_glb; lia.
  - eapply Z.le_trans.
    + eapply Z.le_trans.
      * apply Z.le_min_r.
      * apply Z.le_min_l.
    + lia.
Qed.

(** Coarse bounds for one full [inner_loop] run. *)
Lemma inner_loop_bounds :
  forall a_chars b_char old_cache dist res B,
    Forall (fun x => 0 <= x <= B) old_cache ->
    0 <= dist <= B ->
    0 <= res <= B + 1 ->
    let '(new_cache, d, r) := inner_loop a_chars b_char old_cache dist res in
    Forall (fun x => 0 <= x <= B + 1) new_cache /\
    0 <= d <= B /\
    0 <= r <= B + 1.
Proof.
  induction a_chars as [|a ar IH]; intros b_char old_cache dist res B Hcache Hdist Hres.
  - destruct old_cache; simpl; repeat split; try lia; constructor.
  - destruct old_cache as [|c cs].
    + simpl. repeat split; try lia; constructor.
    + inversion Hcache as [|? ? Hc Hcs]; subst.
      simpl.
      set (bDistance := if (b_char =? a)%Z then dist else dist + 1).
      set (new_result := dp_min res c bDistance).
      assert (HbDist : 0 <= bDistance <= B + 1).
      { subst bDistance. exact (bDistance_bounds b_char a dist B Hdist). }
      assert (Hnew : 0 <= new_result <= B + 1).
      { subst new_result. exact (dp_min_bounds res c bDistance B Hres Hc HbDist). }
      specialize (IH b_char cs c new_result B Hcs Hc Hnew).
      destruct (inner_loop ar b_char cs c new_result) as [[rc fd] fr] eqn:Hi.
      simpl in IH.
      destruct IH as [Hrc [Hfd Hfr]].
      split.
      * constructor; auto.
      * split; auto.
Qed.

Lemma inner_loop_n_bounds :
  forall a_chars b_char old_cache dist res n B,
    Forall (fun x => 0 <= x <= B) old_cache ->
    0 <= dist <= B ->
    0 <= res <= B + 1 ->
    let '(prefix, d, r) := inner_loop_n a_chars b_char old_cache dist res n in
    Forall (fun x => 0 <= x <= B + 1) prefix /\
    0 <= d <= B /\
    0 <= r <= B + 1.
Proof.
  intros a_chars b_char old_cache dist res n B.
  revert a_chars b_char old_cache dist res B.
  induction n as [|n IH]; intros a_chars b_char old_cache dist res B Hcache Hdist Hres.
  - rewrite inner_loop_n_zero.
    split; [constructor|]. split; auto.
  - destruct a_chars as [|a ar].
    + simpl. split; [constructor|]. split; auto.
    + destruct old_cache as [|c cs].
      * simpl. split; [constructor|]. split; auto.
      * inversion Hcache as [|? ? Hc Hcs]; subst.
        simpl.
        set (bDistance := if (b_char =? a)%Z then dist else dist + 1).
        set (new_result := dp_min res c bDistance).
        assert (HbDist : 0 <= bDistance <= B + 1).
        { subst bDistance. exact (bDistance_bounds b_char a dist B Hdist). }
        assert (Hnew : 0 <= new_result <= B + 1).
        { subst new_result. exact (dp_min_bounds res c bDistance B Hres Hc HbDist). }
        specialize (IH ar b_char cs c new_result B Hcs Hc Hnew).
        destruct (inner_loop_n ar b_char cs c new_result n) as [[rc fd] fr] eqn:Hi.
        simpl in IH.
        destruct IH as [Hrc [Hfd Hfr]].
        split.
        { constructor; [exact Hnew | exact Hrc]. }
        { split; [exact Hfd | exact Hfr]. }
Qed.

(** Coarse bounds for the outer cache after [k] rows. *)
Lemma outer_cache_bounds_coarse :
  forall a_chars b_chars la k,
    0 <= la ->
    Forall (fun x => 0 <= x <= la + Z.of_nat k)
      (outer_cache a_chars b_chars (init_cache la) k).
Proof.
  intros a_chars b_chars la k Hla.
  induction k as [|k IH].
  - simpl.
    replace (la + 0) with la by lia.
    apply init_cache_bounds; lia.
  - simpl.
    set (prev := outer_cache a_chars b_chars (init_cache la) k).
    set (b_j := nth k b_chars 0).
    unfold process_row.
    destruct (inner_loop a_chars b_j prev (Z.of_nat k) (Z.of_nat k))
      as [[new_cache fd] fr] eqn:Hloop.
    simpl.
    pose proof (inner_loop_bounds a_chars b_j prev (Z.of_nat k) (Z.of_nat k)
                    (la + Z.of_nat k) IH) as Hstep.
    assert (Hkdist : 0 <= Z.of_nat k <= la + Z.of_nat k) by lia.
    assert (Hkres : 0 <= Z.of_nat k <= la + Z.of_nat k + 1) by lia.
    specialize (Hstep Hkdist Hkres).
    rewrite Hloop in Hstep.
    simpl in Hstep.
    destruct Hstep as [Hnew _].
    eapply (@Forall_impl Z
              (fun x => 0 <= x <= la + Z.of_nat k + 1)
              (fun x => 0 <= x <= la + Z.of_nat (S k))).
    + intros x Hx.
      rewrite Nat2Z.inj_succ.
      lia.
    + exact Hnew.
Qed.

(** Outer-cache bounds specialized to [k : Z] using [Z.to_nat]. *)
Lemma outer_cache_bounds_coarse_Z :
  forall a_contents b_contents la k,
    0 <= la ->
    0 <= k ->
    Forall (fun x => 0 <= x <= la + k)
      (outer_cache (a_Z a_contents) (b_Z b_contents) (init_cache la) (Z.to_nat k)).
Proof.
  intros a_contents b_contents la k Hla Hk.
  pose proof
    (outer_cache_bounds_coarse (a_Z a_contents) (b_Z b_contents)
       la (Z.to_nat k) Hla) as Htmp.
  rewrite Z2Nat.id in Htmp by lia.
  exact Htmp.
Qed.

(** Derive [dist]/[res] coarse bounds from the inner-loop invariant state. *)
Lemma inner_loop_inv_state_bounds :
  forall a_contents b_contents la k old_cache b_char idx dist res,
    old_cache =
      outer_cache (a_Z a_contents) (b_Z b_contents) (init_cache la) (Z.to_nat k) ->
    0 <= la ->
    0 <= k ->
    (let '(prefix, d, r) :=
       inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
     dist = d /\ res = r /\ Zlength prefix = idx) ->
    0 <= dist <= la + k /\ 0 <= res <= la + k + 1.
Proof.
  intros a_contents b_contents la k old_cache b_char idx dist res Hold Hla Hk Hinv.
  subst old_cache.
  pose proof (outer_cache_bounds_coarse_Z a_contents b_contents la k Hla Hk) as Hold_bounds.
  assert (HkB : 0 <= k <= la + k) by lia.
  assert (HkB1 : 0 <= k <= la + k + 1) by lia.
  pose proof
    (inner_loop_n_bounds (a_Z a_contents) b_char
       (outer_cache (a_Z a_contents) (b_Z b_contents) (init_cache la) (Z.to_nat k))
       k k (Z.to_nat idx) (la + k) Hold_bounds HkB HkB1) as Hb.
  destruct (inner_loop_n (a_Z a_contents) b_char
              (outer_cache (a_Z a_contents) (b_Z b_contents) (init_cache la) (Z.to_nat k))
              k k (Z.to_nat idx)) as [[prefix d] r] eqn:Hinner.
  simpl in Hb, Hinv.
  destruct Hb as [_ [Hd Hr]].
  destruct Hinv as [Hdist_eq [Hres_eq _]].
  split; [rewrite Hdist_eq; exact Hd | rewrite Hres_eq; exact Hr].
Qed.

(** Current cache cell at [idx] under the inner-loop invariant representation. *)
Lemma cache_current_from_inner_inv :
  forall a_contents old_cache b_char k idx dist res c_i,
    c_i = Znth idx old_cache ->
    (let '(prefix, d, r) :=
       inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
     dist = d /\ res = r /\ Zlength prefix = idx) ->
    0 <= idx < Zlength old_cache ->
    Znth idx
      (let '(prefix, _, _) :=
         inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
       cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
    = Vlong (Int64.repr c_i).
Proof.
  intros a_contents old_cache b_char k idx dist res c_i Hci Hinv Hidx.
  subst c_i.
  destruct (inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx))
    as [[prefix d] r] eqn:Hinner.
  simpl in Hinv.
  destruct Hinv as [_ [_ Hprefix_len]].
  apply cache_current_Znth; [exact Hprefix_len | exact Hidx].
Qed.

(** Integer comparison helpers for [Int64.ltu] on bounded [Z] values. *)
Lemma int64_ltu_repr_true_iff :
  forall x y,
    0 <= x <= Int64.max_unsigned ->
    0 <= y <= Int64.max_unsigned ->
    Int64.ltu (Int64.repr x) (Int64.repr y) = true <-> x < y.
Proof.
  intros x y Hx Hy.
  unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y) as [Hxy|Hxy].
  - split; intro H.
    + exact Hxy.
    + reflexivity.
  - split; intro H.
    + discriminate.
    + lia.
Qed.

Lemma int64_ltu_repr_false_iff :
  forall x y,
    0 <= x <= Int64.max_unsigned ->
    0 <= y <= Int64.max_unsigned ->
    Int64.ltu (Int64.repr x) (Int64.repr y) = false <-> y <= x.
Proof.
  intros x y Hx Hy.
  unfold Int64.ltu.
  rewrite !Int64.unsigned_repr by lia.
  destruct (zlt x y) as [Hxy|Hxy].
  - split; intro H.
    + discriminate.
    + exfalso. lia.
  - split; intro H.
    + lia.
    + reflexivity.
Qed.

Ltac from_typed_true_ltu H :=
  lazymatch type of H with
  | Int64.ltu (Int64.repr ?x) (Int64.repr ?y) = true =>
      let Hiff := fresh "Hiff" in
      pose proof (int64_ltu_repr_true_iff x y ltac:(lia) ltac:(lia)) as Hiff;
      apply Hiff in H;
      clear Hiff
  | _ =>
      apply typed_true_of_bool in H;
      from_typed_true_ltu H
  end.

Ltac from_typed_false_ltu H :=
  lazymatch type of H with
  | Int64.ltu (Int64.repr ?x) (Int64.repr ?y) = false =>
      let Hiff := fresh "Hiff" in
      pose proof (int64_ltu_repr_false_iff x y ltac:(lia) ltac:(lia)) as Hiff;
      apply Hiff in H;
      clear Hiff
  | _ =>
      apply typed_false_of_bool in H;
      from_typed_false_ltu H
  end.

(* ================================================================ *)
(*                    BODY PROOF                                      *)
(* ================================================================ *)

(** The main verification theorem: the C function [levenshtein_n]
    satisfies its specification. *)
Lemma body_levenshtein_n :
  semax_body Vprog Gprog f_levenshtein_n levenshtein_n_spec.
Proof.
  start_function.
  forward. (* result = 0 *)

  (* ==== if (length == 0) return bLength ==== *)
  forward_if.
  { forward. entailer!.
    assert (Hla0 : Zlength a_contents = 0).
    { change Int64.zero with (Int64.repr 0) in H5.
      apply (f_equal Int64.unsigned) in H5.
      rewrite !Int64.unsigned_repr in H5 by rep_lia.
      exact H5. }
    unfold lev_dp, bytes_to_Z.
    rewrite !Zlength_map, Hla0. reflexivity. }

  (* ==== if (bLength == 0) return length ==== *)
  forward_if.
  { forward. entailer!.
    assert (Hlb0 : Zlength b_contents = 0).
    { change Int64.zero with (Int64.repr 0) in H6.
      apply (f_equal Int64.unsigned) in H6.
      rewrite !Int64.unsigned_repr in H6 by rep_lia.
      exact H6. }
    assert (Hla_ne : Zlength a_contents <> 0).
    { intro Heq. apply H5. f_equal. exact Heq. }
    unfold lev_dp, bytes_to_Z.
    rewrite !Zlength_map, Hlb0.
    replace (Zlength a_contents =? 0)%Z with false
      by (symmetry; apply Z.eqb_neq; exact Hla_ne).
    reflexivity. }

  (* ==== cache = calloc(length, sizeof(size_t)) ==== *)
  forward_call (la, gv).
  { assert (Hne: la <> 0)
      by (intro Heq; apply H5; f_equal; exact Heq).
    split; [lia | apply H4; lia]. }
  Intros cache_ptr.
  forward. (* index = 0 *)

  (* ==== Init loop ==== *)
  forward_while (init_loop_inv sh_a sh_b a_ptr b_ptr cache_ptr
                               a_contents b_contents la lb gv).
  - (* entry: i=0 *)
    Exists 0. entailer!.
    simpl. unfold data_at_. cancel.
  - (* tc_expr *) entailer!.
  - (* body *)
    forward.
    + assert (Hi : 0 <= i < la).
      { assert (Hi0Le : 0 <= i <= la).
        { match goal with
          | Hinv : 0 <= i <= la |- _ => exact Hinv
          end. }
        destruct Hi0Le as [Hi0 HiLe].
        apply Int64.ltu_inv in HRE as [_ Hlt].
        split; [assumption|].
        rewrite !Int64.unsigned_repr in Hlt by rep_lia.
        lia. }
      entailer!.
    + forward.
      Exists (i + 1).
      change (Int.signed (Int.repr 1)) with 1.
      replace (Int64.add (Int64.repr i) (Int64.repr 1))
        with (Int64.repr (i + 1)).
      2:{ rewrite Int64.add_unsigned.
          rewrite !Int64.unsigned_repr by rep_lia.
          reflexivity. }
      rewrite (init_loop_cache_update la i).
      2:{ destruct H1; lia. }
      2:{ assert (Hi0Le : 0 <= i <= la).
          { match goal with
            | Hinv : 0 <= i <= la |- _ => exact Hinv
            end. }
          destruct Hi0Le as [Hi0 HiLe].
          apply Int64.ltu_inv in HRE as [_ Hlt].
          split; [assumption|].
          rewrite !Int64.unsigned_repr in Hlt by rep_lia.
          lia. }
      assert (Hi_lt : i < la).
      { apply Int64.ltu_inv in HRE as [_ Hlt].
        rewrite !Int64.unsigned_repr in Hlt by rep_lia.
        lia. }
      entailer!; try (split; lia); try reflexivity.
  - (* exit: init loop done, continue with rest of function *)

    (* ==== bIndex = 0 ==== *)
    forward.

    (* ==== Outer loop ==== *)
    forward_while (outer_loop_inv sh_a sh_b a_ptr b_ptr cache_ptr
                                  a_contents b_contents la lb gv).
    + (* entry: k=0 *)
      Exists 0. Exists (Vlong (Int64.repr 0)).
      assert (Hi_eq : i = la).
      { assert (Hge : la <= i).
        { unfold Int64.ltu in HRE.
          rewrite !Int64.unsigned_repr in HRE by rep_lia.
          destruct (zlt i la); [discriminate|lia]. }
        lia. }
      subst i.
      change (Int.signed (Int.repr 0)) with 0.
      rewrite (Zfirstn_same _ la (init_cache la)).
      2:{ rewrite init_cache_Zlength by lia. lia. }
      rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
      entailer!; simpl; auto.
    + (* tc_expr *) entailer!.
    + (* body *)
      assert (Hk : 0 <= k < lb).
      { assert (Hk0Le : 0 <= k <= lb).
        { match goal with
          | Hinv : 0 <= k <= lb |- _ => exact Hinv
          end. }
        destruct Hk0Le as [Hk0 HkLe].
        apply Int64.ltu_inv in HRE0 as [_ Hlt].
        rewrite !Int64.unsigned_repr in Hlt by rep_lia.
        lia. }
      assert (Hk_b : 0 <= k < Zlength b_contents) by (rewrite H0; lia).
      forward. (* t'3 load *)
      forward. (* code set *)
      forward. (* result = bIndex *)
      forward. (* distance = bIndex *)
      forward. (* bIndex++ *)
      forward. (* index = 0 *)
      set (old_cache := outer_cache (a_Z a_contents) (b_Z b_contents)
                                     (init_cache la) (Z.to_nat k)).
      set (b_char := Byte.unsigned (Znth k b_contents)).
      forward_while (inner_loop_inv sh_a sh_b a_ptr b_ptr cache_ptr
                                    a_contents b_contents
                                    la lb k old_cache b_char gv).
      * Exists 0. Exists k. Exists k.
        unfold b_char, old_cache.
        rewrite Byte.repr_unsigned.
        change (Int.signed (Int.repr 0)) with 0.
        change (Int.signed (Int.repr 1)) with 1.
        replace (Int64.add (Int64.repr k) (Int64.repr 1))
          with (Int64.repr (k + 1)).
        2:{ rewrite Int64.add_unsigned.
            rewrite !Int64.unsigned_repr by rep_lia.
            reflexivity. }
        assert (Hlen_ai : length (a_Z a_contents) = length (init_cache la)).
        { unfold a_Z, bytes_to_Z, init_cache.
          rewrite !length_map, length_seq.
          apply (f_equal Z.to_nat) in H.
          rewrite ZtoNat_Zlength in H.
          exact H. }
        assert (Hold_len : Zlength old_cache = la).
        { unfold old_cache.
          rewrite outer_cache_length with (init := init_cache la); [|exact Hlen_ai].
          apply init_cache_Zlength. lia. }
        rewrite inner_loop_n_zero.
        entailer!; try (repeat split; reflexivity).
      * entailer!.
      * assert (Hidx : 0 <= idx < la).
        { destruct H10 as [Hidx0 HidxLe].
          apply Int64.ltu_inv in HRE1 as [_ Hlt].
          rewrite !Int64.unsigned_repr in Hlt by rep_lia.
          split; [assumption|lia]. }
        assert (Hidx_a : 0 <= idx < Zlength a_contents) by (rewrite H; exact Hidx).
        forward. (* t'2 = a[index] *)
        set (a_i := Znth idx (a_Z a_contents)).
        forward_if
          (EX bd : Z,
           PROP (bd = (if (b_char =? a_i)%Z then dist else dist + 1)%Z)
           LOCAL (temp _bDistance (Vlong (Int64.repr bd));
                  temp _t'2 (Vbyte (Znth idx a_contents));
                  temp _index (Vlong (Int64.repr idx));
                  temp _distance (Vlong (Int64.repr dist));
                  temp _result (Vlong (Int64.repr res));
                  temp _code (Vint (Int.repr (Byte.signed (Byte.repr b_char))));
                  temp _bIndex (Vlong (Int64.repr (k + 1)));
                  temp _cache cache_ptr;
                  temp _length (Vlong (Int64.repr la));
                  temp _bLength (Vlong (Int64.repr lb));
                  temp _a a_ptr;
                  temp _b b_ptr;
                  gvars gv)
           SEP (mem_mgr gv;
                malloc_token Ews (tarray tulong la) cache_ptr;
                data_at Ews (tarray tulong la)
                  (let '(prefix, _, _) :=
                     inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                   cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                  cache_ptr;
                data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
                data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr)).
        -- forward.
           Exists dist.
           entailer!.
           subst a_i. unfold a_Z, bytes_to_Z.
           rewrite Znth_map by exact Hidx_a.
           assert (Hbchar_range : 0 <= b_char <= Byte.max_unsigned).
           { unfold b_char. apply Byte.unsigned_range_2. }
           assert (Hb_eq : b_char = Byte.unsigned (Znth idx a_contents)).
           { match goal with
             | Hcode : Byte.repr b_char = Znth idx a_contents |- _ =>
                 apply (f_equal Byte.unsigned) in Hcode;
                 rewrite Byte.unsigned_repr in Hcode by exact Hbchar_range;
                 exact Hcode
             end. }
           rewrite Hb_eq, Z.eqb_refl. reflexivity.
        -- forward.
           Exists (dist + 1).
           entailer!.
           subst a_i. unfold a_Z, bytes_to_Z.
           rewrite Znth_map by exact Hidx_a.
           match goal with
           | Hcode : Byte.repr b_char <> Znth idx a_contents |- _ =>
               destruct (Z.eqb_spec b_char (Byte.unsigned (Znth idx a_contents)))
                 as [Heq | Hneq];
               [exfalso; apply Hcode; rewrite Heq; apply Byte.repr_unsigned
               |reflexivity]
           end.
        -- Intros bd.
           forward. (* distance = cache[index] *)
           ++ destruct (inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx))
                as [[prefix d] r] eqn:Hinner.
              simpl in H12.
              destruct H12 as [_ [_ Hprefix_len]].
              assert (Hidx_old : 0 <= idx < Zlength old_cache).
              { rewrite H11. exact Hidx. }
              assert (Hznth_cur :
                Znth idx
                  (cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                = Vlong (Int64.repr (Znth idx old_cache))).
              { apply cache_current_Znth; [exact Hprefix_len | exact Hidx_old]. }
              simpl.
              setoid_rewrite Hznth_cur.
              entailer!.
           ++ fastforward.
              set (c_i := Znth idx old_cache).
              forward_if
                (EX new_res : Z,
                 PROP (new_res = dp_min res c_i bd)
                 LOCAL (temp _result (Vlong (Int64.repr new_res));
                        temp _distance
                          (Znth idx
                             (let '(prefix, _, _) :=
                                inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                              cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache)));
                        temp _bDistance (Vlong (Int64.repr bd));
                        temp _t'2 (Vbyte (Znth idx a_contents));
                        temp _index (Vlong (Int64.repr idx));
                        temp _code (Vbyte (Byte.repr b_char));
                        temp _bIndex (Vlong (Int64.repr (k + 1)));
                        temp _cache cache_ptr;
                        temp _length (Vlong (Int64.repr la));
                        temp _bLength (Vlong (Int64.repr lb));
                        temp _a a_ptr;
                        temp _b b_ptr;
                        gvars gv)
                 SEP (mem_mgr gv;
                      malloc_token Ews (tarray tulong la) cache_ptr;
                      data_at Ews (tarray tulong la)
                        (let '(prefix, _, _) :=
                           inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                         cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                        cache_ptr;
                      data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
                      data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr)).
              {
                forward_if
                  (EX new_res : Z,
                   PROP (new_res = dp_min res c_i bd)
                   LOCAL (temp _result (Vlong (Int64.repr new_res));
                          temp _distance
                            (Znth idx
                               (let '(prefix, _, _) :=
                                  inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                                cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache)));
                          temp _bDistance (Vlong (Int64.repr bd));
                          temp _t'2 (Vbyte (Znth idx a_contents));
                          temp _index (Vlong (Int64.repr idx));
                          temp _code (Vbyte (Byte.repr b_char));
                          temp _bIndex (Vlong (Int64.repr (k + 1)));
                          temp _cache cache_ptr;
                          temp _length (Vlong (Int64.repr la));
                          temp _bLength (Vlong (Int64.repr lb));
                          temp _a a_ptr;
                          temp _b b_ptr;
                          gvars gv)
                   SEP (mem_mgr gv;
                        malloc_token Ews (tarray tulong la) cache_ptr;
                        data_at Ews (tarray tulong la)
                          (let '(prefix, _, _) :=
                             inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                           cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                          cache_ptr;
                        data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
                        data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr)).
                { forward.
                  assert (Hidx_old : 0 <= idx < Zlength old_cache).
                  { rewrite H11. exact Hidx. }
                  assert (Hold_bounds : Forall (fun x => 0 <= x <= la + k) old_cache).
                  { unfold old_cache.
                    apply outer_cache_bounds_coarse_Z; [exact (proj1 H1) | exact (proj1 Hk)]. }
                  assert (Hci_bounds : 0 <= c_i <= la + k).
                  { unfold c_i.
                    apply (proj1 (Forall_Znth old_cache (fun x => 0 <= x <= la + k)));
                    [exact Hold_bounds | exact Hidx_old]. }
                  assert (Hdist_res_bounds : 0 <= dist <= la + k /\ 0 <= res <= la + k + 1).
                  { eapply inner_loop_inv_state_bounds.
                    - unfold old_cache; reflexivity.
                    - exact (proj1 H1).
                    - exact (proj1 Hk).
                    - exact H12. }
                  assert (Hbd_bounds : 0 <= bd <= la + k + 1).
                  { rewrite H13.
                    destruct (b_char =? a_i)%Z; lia. }
                  assert (Hmax_k1 : la + k + 1 <= Int64.max_unsigned) by lia.
                  assert (Hres_range : 0 <= res <= Int64.max_unsigned) by lia.
                  assert (Hci_range : 0 <= c_i <= Int64.max_unsigned) by lia.
                  assert (Hbd_range : 0 <= bd <= Int64.max_unsigned) by lia.
                  Exists (Int64.unsigned (Int64.add (Int64.repr res) (Int64.repr 1))).
                  assert (Hcur :
                    Znth idx
                      (let '(prefix, _, _) :=
                         inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                       cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                    = Vlong (Int64.repr c_i)).
                  { eapply cache_current_from_inner_inv.
                    - unfold c_i; reflexivity.
                    - exact H12.
                    - exact Hidx_old. }
                  setoid_rewrite Hcur in H14.
                  simpl in H14.
                  assert (Hci_gt_res : res < c_i).
                  { from_typed_true_ltu H14. exact H14. }
                  assert (Hbd_gt_res : res < bd).
                  { from_typed_true_ltu H15. exact H15. }
                  assert (Hdp : dp_min res c_i bd = res + 1).
                  { unfold dp_min.
                    assert (Hgt_ci : (c_i >? res)%Z = true) by (apply Z.gtb_lt; lia).
                    assert (Hgt_bd : (bd >? res)%Z = true) by (apply Z.gtb_lt; lia).
                    rewrite Hgt_ci, Hgt_bd.
                    lia. }
                  assert (Hres1_range : 0 <= res + 1 <= Int64.max_unsigned) by lia.
                  entailer!. }
                { forward.
                  assert (Hidx_old : 0 <= idx < Zlength old_cache).
                  { rewrite H11. exact Hidx. }
                  assert (Hold_bounds :
                    Forall (fun x => 0 <= x <= la + k) old_cache).
                  { unfold old_cache.
                    apply outer_cache_bounds_coarse_Z; [exact (proj1 H1) | exact (proj1 Hk)]. }
                  assert (Hci_bounds : 0 <= c_i <= la + k).
                  { unfold c_i.
                    apply (proj1 (Forall_Znth old_cache
                             (fun x => 0 <= x <= la + k)));
                    [exact Hold_bounds | exact Hidx_old]. }
                  assert (Hdist_res_bounds :
                    0 <= dist <= la + k /\
                    0 <= res <= la + k + 1).
                  { eapply inner_loop_inv_state_bounds.
                    - unfold old_cache; reflexivity.
                    - exact (proj1 H1).
                    - exact (proj1 Hk).
                    - exact H12. }
                  assert (Hbd_bounds :
                    0 <= (if b_char =? a_i then dist else dist + 1)
                      <= la + k + 1).
                  { destruct Hdist_res_bounds as [Hdist_bounds _].
                    destruct (b_char =? a_i)%Z; lia. }
                  assert (Hmax_k1 : la + k + 1 <= Int64.max_unsigned) by lia.
                  assert (Hres_range : 0 <= res <= Int64.max_unsigned) by lia.
                  assert (Hci_range : 0 <= c_i <= Int64.max_unsigned) by lia.
                  assert (Hbd_range :
                    0 <= (if b_char =? a_i then dist else dist + 1) <= Int64.max_unsigned) by lia.
                  assert (Hcur :
                    Znth idx
                      (let '(prefix, _, _) :=
                         inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                       cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                    = Vlong (Int64.repr c_i)).
                  { eapply cache_current_from_inner_inv.
                    - unfold c_i; reflexivity.
                    - exact H12.
                    - exact Hidx_old. }
                  setoid_rewrite Hcur in H14.
                  simpl in H14.
                  assert (Hci_gt_res : res < c_i).
                  { from_typed_true_ltu H14. exact H14. }
                  assert (Hbd_le_res :
                    (if b_char =? a_i then dist else dist + 1) <= res).
                  { rewrite H13 in H15.
                    from_typed_false_ltu H15.
                    exact H15. }
                  Exists (if b_char =? a_i then dist else dist + 1).
                  entailer!.
                  unfold dp_min.
                  assert (Hgt_ci : (c_i >? res)%Z = true) by (apply Z.gtb_lt; lia).
                  assert (Hgt_bd : ((if b_char =? a_i then dist else dist + 1) >? res)%Z = false).
                  { destruct ((if b_char =? a_i then dist else dist + 1) >? res)%Z eqn:Hcmp.
                    - apply Z.gtb_lt in Hcmp. lia.
                    - reflexivity. }
                  rewrite Hgt_ci, Hgt_bd.
                  reflexivity. }
              }
              {
                forward_if
                  (EX new_res : Z,
                   PROP (new_res = dp_min res c_i bd)
                   LOCAL (temp _result (Vlong (Int64.repr new_res));
                          temp _distance
                            (Znth idx
                               (let '(prefix, _, _) :=
                                  inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                                cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache)));
                          temp _bDistance (Vlong (Int64.repr bd));
                          temp _t'2 (Vbyte (Znth idx a_contents));
                          temp _index (Vlong (Int64.repr idx));
                          temp _code (Vbyte (Byte.repr b_char));
                          temp _bIndex (Vlong (Int64.repr (k + 1)));
                          temp _cache cache_ptr;
                          temp _length (Vlong (Int64.repr la));
                          temp _bLength (Vlong (Int64.repr lb));
                          temp _a a_ptr;
                          temp _b b_ptr;
                          gvars gv)
                   SEP (mem_mgr gv;
                        malloc_token Ews (tarray tulong la) cache_ptr;
                        data_at Ews (tarray tulong la)
                          (let '(prefix, _, _) :=
                             inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                           cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                          cache_ptr;
                        data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
                        data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr)).
                { forward.
                  assert (Hidx_old : 0 <= idx < Zlength old_cache).
                  { rewrite H11. exact Hidx. }
                  assert (Hold_bounds : Forall (fun x => 0 <= x <= la + k) old_cache).
                  { unfold old_cache.
                    apply outer_cache_bounds_coarse_Z; [exact (proj1 H1) | exact (proj1 Hk)]. }
                  assert (Hci_bounds : 0 <= c_i <= la + k).
                  { unfold c_i.
                    apply (proj1 (Forall_Znth old_cache (fun x => 0 <= x <= la + k)));
                    [exact Hold_bounds | exact Hidx_old]. }
                  assert (Hdist_res_bounds :
                    0 <= dist <= la + k /\ 0 <= res <= la + k + 1).
                  { eapply inner_loop_inv_state_bounds.
                    - unfold old_cache; reflexivity.
                    - exact (proj1 H1).
                    - exact (proj1 Hk).
                    - exact H12. }
                  assert (Hbd_bounds :
                    0 <= (if b_char =? a_i then dist else dist + 1) <= la + k + 1).
                  { destruct Hdist_res_bounds as [Hdist_bounds _].
                    destruct (b_char =? a_i)%Z; lia. }
                  assert (Hmax_k1 : la + k + 1 <= Int64.max_unsigned) by lia.
                  assert (Hci_range : 0 <= c_i <= Int64.max_unsigned) by lia.
                  assert (Hres_range : 0 <= res <= Int64.max_unsigned) by lia.
                  assert (Hbd_range :
                    0 <= (if b_char =? a_i then dist else dist + 1) <= Int64.max_unsigned) by lia.
                  assert (Hcur :
                    Znth idx
                      (let '(prefix, _, _) :=
                         inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                       cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                    = Vlong (Int64.repr c_i)).
                  { eapply cache_current_from_inner_inv.
                    - unfold c_i; reflexivity.
                    - exact H12.
                    - exact Hidx_old. }
                  setoid_rewrite Hcur in H14.
                  setoid_rewrite Hcur in H15.
                  simpl in H14, H15.
                  assert (Hci_le_res : c_i <= res).
                  { from_typed_false_ltu H14. exact H14. }
                  assert (Hbd_gt_ci : c_i < (if b_char =? a_i then dist else dist + 1)).
                  { rewrite H13 in H15.
                    from_typed_true_ltu H15.
                    exact H15. }
                  assert (Hdp :
                    dp_min res c_i (if b_char =? a_i then dist else dist + 1) = c_i + 1).
                  { unfold dp_min.
                    assert (Hgt1 : (c_i >? res)%Z = false).
                    { destruct (c_i >? res)%Z eqn:Hcmp.
                      - apply Z.gtb_lt in Hcmp. lia.
                      - reflexivity. }
                    assert (Hgt2 :
                      ((if b_char =? a_i then dist else dist + 1) >? c_i)%Z = true)
                      by (apply Z.gtb_lt; lia).
                    rewrite Hgt1, Hgt2.
                    lia. }
                  assert (Hci1_range : 0 <= c_i + 1 <= Int64.max_unsigned) by lia.
                  assert (Hadd :
                    force_val
                      (both_long (fun n1 n2 : int64 => Some (Vlong (Int64.add n1 n2)))
                         sem_cast_pointer (sem_cast_i2l Signed)
                         (Znth idx
                            (let '(prefix, _, _) :=
                               inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                             cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache)))
                         (Vint (Int.repr 1)))
                    = Vlong (Int64.repr (c_i + 1))).
                  { rewrite Hcur.
                    simpl.
                    rewrite Int64.add_unsigned.
                    rewrite !Int64.unsigned_repr by lia.
                    reflexivity. }
                  Exists (Int64.unsigned (Int64.add (Int64.repr c_i) (Int64.repr 1))).
                  replace
                    (force_val
                       (sem_binary_operation' Oadd tulong tint
                          (Znth idx
                             (let '(prefix, _, _) :=
                                inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                              cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache)))
                          (Vint (Int.repr 1))))
                    with
                    (Vlong
                       (Int64.repr
                          (Int64.unsigned (Int64.add (Int64.repr c_i) (Int64.repr 1))))).
                  2:{ unfold sem_binary_operation'.
                      simpl.
                      replace
                        (force_val
                           (both_long (fun n1 n2 : int64 => Some (Vlong (Int64.add n1 n2)))
                              sem_cast_pointer (sem_cast_i2l Signed)
                              (Znth idx
                                 (let '(prefix, _, _) :=
                                    inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                                  cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache)))
                              (Vint (Int.repr 1))))
                        with (Vlong (Int64.repr (c_i + 1))).
                      f_equal.
                      assert (Hmod_ci : Int64.Z_mod_modulus c_i = c_i).
                      { rewrite Int64.Z_mod_modulus_eq.
                        apply Z.mod_small.
                        unfold Int64.max_unsigned in Hci_range.
                        lia. }
                      rewrite Hmod_ci.
                      rewrite Int64.Z_mod_modulus_eq.
                      rewrite Z.mod_small.
                      2:{ unfold Int64.max_unsigned in Hci1_range.
                          lia. }
                      reflexivity. }
                  entailer!. }
                { forward.
                  assert (Hidx_old2 : 0 <= idx < Zlength old_cache).
                  { rewrite H11. exact Hidx. }
                  assert (Hold_bounds :
                    Forall (fun x => 0 <= x <= la + k) old_cache).
                  { unfold old_cache.
                    apply outer_cache_bounds_coarse_Z; [exact (proj1 H1) | exact (proj1 Hk)]. }
                  assert (Hci_bounds : 0 <= c_i <= la + k).
                  { unfold c_i.
                    apply (proj1 (Forall_Znth old_cache (fun x => 0 <= x <= la + k)));
                    [exact Hold_bounds | exact Hidx_old2]. }
                  assert (Hdist_res_bounds :
                    0 <= dist <= la + k /\ 0 <= res <= la + k + 1).
                  { eapply inner_loop_inv_state_bounds.
                    - unfold old_cache; reflexivity.
                    - exact (proj1 H1).
                    - exact (proj1 Hk).
                    - exact H12. }
                  assert (Hbd_bounds : 0 <= bd <= la + k + 1).
                  { rewrite H13.
                    destruct (b_char =? a_i)%Z; lia. }
                  assert (Hmax_k1 : la + k + 1 <= Int64.max_unsigned) by lia.
                  assert (Hres_range : 0 <= res <= Int64.max_unsigned) by lia.
                  assert (Hci_range : 0 <= c_i <= Int64.max_unsigned) by lia.
                  assert (Hbd_range : 0 <= bd <= Int64.max_unsigned) by lia.
                  assert (Hcur :
                    Znth idx
                      (let '(prefix, _, _) :=
                         inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx) in
                       cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                    = Vlong (Int64.repr c_i)).
                  { eapply cache_current_from_inner_inv.
                    - unfold c_i; reflexivity.
                    - exact H12.
                    - exact Hidx_old2. }
                  setoid_rewrite Hcur in H14.
                  setoid_rewrite Hcur in H15.
                  simpl in H14, H15.
                  assert (Hci_le_res : c_i <= res).
                  { from_typed_false_ltu H14. exact H14. }
                  assert (Hbd_le_ci : bd <= c_i).
                  { from_typed_false_ltu H15. exact H15. }
                  assert (Hif_le_ci : (if b_char =? a_i then dist else dist + 1) <= c_i).
                  { rewrite <- H13. exact Hbd_le_ci. }
                  Exists bd.
                  entailer!.
                  unfold dp_min.
                  assert (Hgt1 : (c_i >? res)%Z = false).
                  { destruct (c_i >? res)%Z eqn:Hcmp.
                    - apply Z.gtb_lt in Hcmp. lia.
                    - reflexivity. }
                  assert (Hgt2 : ((if b_char =? a_i then dist else dist + 1) >? c_i)%Z = false).
                  { destruct ((if b_char =? a_i then dist else dist + 1) >? c_i)%Z eqn:Hcmp.
                    - apply Z.gtb_lt in Hcmp. lia.
                    - reflexivity. }
                  rewrite Hgt1, Hgt2.
                  reflexivity. }
              }
              { Intros new_res.
                forward.
                forward.
                Exists (idx + 1, c_i, new_res).
                assert (Hidx_old : 0 <= idx < Zlength old_cache).
                { rewrite H11. exact Hidx. }
                destruct (inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat idx))
                  as [[prefix d] r] eqn:Hinner.
                simpl in H12.
                destruct H12 as [Hdist_eq [Hres_eq Hprefix_len]].
                assert (Hcur :
                  Znth idx
                    (cache_to_val prefix ++ cache_to_val (skipn (Z.to_nat idx) old_cache))
                  = Vlong (Int64.repr c_i)).
                { unfold c_i.
                  apply cache_current_Znth; [exact Hprefix_len | exact Hidx_old]. }
                assert (Hidx_aZ : 0 <= idx < Zlength (a_Z a_contents)).
                { unfold a_Z, bytes_to_Z.
                  rewrite Zlength_map.
                  exact Hidx_a. }
                assert (Hlenz : Zlength (a_Z a_contents) = Zlength old_cache).
                { unfold a_Z, bytes_to_Z.
                  rewrite Zlength_map.
                  lia. }
                pose proof (inner_loop_n_step_Z (a_Z a_contents) b_char old_cache k k idx
                              Hlenz Hidx_aZ) as Hstep.
                rewrite Hinner in Hstep.
                simpl in Hstep.
                rewrite <- Hdist_eq, <- Hres_eq in Hstep.
                unfold a_i in H13.
                rewrite <- H13 in Hstep.
                unfold c_i in H14.
                rewrite <- H14 in Hstep.
                rewrite (cache_update_step prefix old_cache idx new_res Hprefix_len Hidx_old).
                change (Int.signed (Int.repr 1)) with 1.
                replace (Int64.add (Int64.repr idx) (Int64.repr 1))
                  with (Int64.repr (idx + 1)).
                2:{ rewrite Int64.add_unsigned.
                    rewrite !Int64.unsigned_repr by rep_lia.
                    reflexivity. }
                rewrite Hcur.
                entailer!.
                - split; [lia|].
                  rewrite Hstep.
                  simpl.
                  split; [reflexivity|].
                  split; [reflexivity|].
                  rewrite Zlength_app.
                  rewrite Zlength_cons, Zlength_nil.
                  lia.
                - rewrite Hstep.
                  apply derives_refl. }
      * assert (Hidx_eq : idx = la).
        { destruct H10 as [Hidx0 HidxLe].
          assert (Hge : la <= idx).
          { unfold Int64.ltu in HRE1.
            rewrite !Int64.unsigned_repr in HRE1 by rep_lia.
            destruct (zlt idx la); [discriminate | lia]. }
          lia. }
        subst idx.
        destruct (inner_loop_n (a_Z a_contents) b_char old_cache k k (Z.to_nat la))
          as [[prefix d] r] eqn:Hinner.
        simpl in H12.
        destruct H12 as [Hdist_eq [Hres_eq Hprefix_len]].
        assert (Hla_nat : Z.to_nat la = length (a_Z a_contents)).
        { unfold a_Z, bytes_to_Z.
          rewrite length_map.
          rewrite <- ZtoNat_Zlength.
          rewrite H.
          reflexivity. }
        assert (Hold_nat : length old_cache = Z.to_nat la).
        { rewrite <- ZtoNat_Zlength.
          rewrite H11.
          reflexivity. }
        assert (Hlen_nat : length (a_Z a_contents) = length old_cache) by lia.
        pose proof (inner_loop_n_full (a_Z a_contents) b_char old_cache k k Hlen_nat) as Hfull.
        rewrite Hla_nat in Hinner.
        rewrite Hinner in Hfull.
        destruct (inner_loop (a_Z a_contents) b_char old_cache k k)
          as [[nc fd] fr] eqn:Hloop.
        simpl in Hfull.
        inversion Hfull; subst nc fd fr.
        assert (Hk_map : 0 <= k < Zlength (map Byte.unsigned b_contents)).
        { rewrite Zlength_map. exact Hk_b. }
        assert (Hb_nth : nth (Z.to_nat k) (b_Z b_contents) 0 = b_char).
        { unfold b_char, b_Z, bytes_to_Z.
          rewrite (nth_Znth k (map Byte.unsigned b_contents)); [|exact Hk_map].
          rewrite Znth_map by exact Hk_b.
          reflexivity. }
        assert (Hcache_step :
          outer_cache (a_Z a_contents) (b_Z b_contents) (init_cache la)
            (Z.to_nat (k + 1)) = prefix).
        { rewrite Z2Nat.inj_add by lia.
          rewrite Nat.add_1_r.
          simpl.
          unfold old_cache in Hloop.
          rewrite Hb_nth.
          replace (Z.of_nat (Z.to_nat k)) with k by lia.
          unfold process_row.
          rewrite Hloop.
          reflexivity. }
        assert (Hres_step :
          outer_result (a_Z a_contents) (b_Z b_contents) (init_cache la)
            (Z.to_nat (k + 1)) = r).
        { rewrite Z2Nat.inj_add by lia.
          rewrite Nat.add_1_r.
          simpl.
          unfold old_cache in Hloop.
          rewrite Hb_nth.
          replace (Z.of_nat (Z.to_nat k)) with k by lia.
          unfold process_row.
          rewrite Hloop.
          reflexivity. }
        assert (Hskip_nil : skipn (Z.to_nat la) old_cache = []).
        { rewrite <- Hold_nat.
          apply skipn_all2.
          lia. }
        forward.
        Exists (k + 1, Vlong (Int64.repr res)).
        rewrite Hskip_nil, app_nil_r.
        rewrite <- Hcache_step.
        entailer!.
        lia.
    + (* exit: outer loop done *)

      (* ==== free and return ==== *)
      assert (Hk_eq : k = lb).
      { destruct H7 as [Hk0 HkLe].
        assert (Hge : lb <= k).
        { unfold Int64.ltu in HRE0.
          rewrite !Int64.unsigned_repr in HRE0 by rep_lia.
          destruct (zlt k lb); [discriminate | lia]. }
        lia. }
      subst k.
      forward_call (tarray tulong la, cache_ptr, gv).
      * instantiate (Frame :=
           [data_at sh_a (tarray tschar la) (map Vbyte a_contents) a_ptr;
            data_at sh_b (tarray tschar lb) (map Vbyte b_contents) b_ptr]).
        destruct (eq_dec cache_ptr nullval) as [Hnull | Hnull].
        { subst. entailer!. }
        simpl fold_right_sepcon.
        repeat rewrite sepcon_assoc.
        apply sepcon_derives.
        { apply derives_refl. }
        apply sepcon_derives.
        { apply data_at_data_at_. }
        cancel.
      * forward.
        entailer!.
        unfold lev_dp, bytes_to_Z.
        rewrite !Zlength_map.
        replace (Zlength a_contents =? 0)%Z with false.
        2:{ symmetry; apply Z.eqb_neq.
            intro Heq. apply H5. f_equal. exact Heq. }
        replace (Zlength b_contents =? 0)%Z with false.
        2:{ symmetry; apply Z.eqb_neq.
            intro Heq. apply H6. f_equal. exact Heq. }
        unfold a_Z, b_Z, bytes_to_Z.
        repeat rewrite Zlength_correct.
        rewrite Nat2Z.id.
        reflexivity.
Qed.

(* ================================================================ *)
(*                   PROGRAM CORRECTNESS                              *)
(* ================================================================ *)

(* Program-level function correctness for all internal functions in [prog]. *)
Lemma prog_correct :
  semax_body Vprog Gprog f_levenshtein_n levenshtein_n_spec.
Proof.
  exact body_levenshtein_n.
Qed.

(* ================================================================ *)
(*                    BRIDGE THEOREM                                  *)
(* ================================================================ *)
(* The key theorem connecting the C-faithful functional model to     *)
(* the intrinsically-verified Rocq Levenshtein from Crane PR #17.    *)

(* Bridge status:
   - The VST proof here establishes: C function = lev_dp (Z/byte model).
   - The DP/recursive equivalence bridge is maintained in Crane's
     BridgeDP-style development (row-specification plus reversal argument).
   - End-to-end composition target remains:
       C code -> lev_dp -> levenshtein_computed -> minimality theorem. *)
