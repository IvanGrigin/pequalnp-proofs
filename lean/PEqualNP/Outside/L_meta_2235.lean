import PEqualNP.Defs

-- The tree lemmas adapt L_meta_1942 by npollock14, PR 4373.
-- The star-counting lemmas adapt L_meta_1733 by willakone, PR 3869.

namespace PEqualNP.Outside.L_meta_2235

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

namespace Tree
section Circuit

private def evalFrom {α : Type} (d : α) (op : GateOp → List α → α) (gates : List Gate) (xs : List α) :
    List α :=
  gates.foldl (fun u g => u ++ [op g.op (g.inputs.map fun i => u.getD i d)]) xs

private lemma evalFrom_cons {α : Type} (d : α) (op : GateOp → List α → α) (g : Gate) (gs : List Gate)
    (xs : List α) :
    evalFrom d op (g :: gs) xs = evalFrom d op gs
      (xs ++ [op g.op (g.inputs.map fun i => xs.getD i d)]) := rfl

private lemma evalFrom_length {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) : (evalFrom d op gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [evalFrom]
  | cons g gs ih => rw [evalFrom_cons, ih]; simp; omega

private lemma evalFrom_input {α : Type} (d : α) (op : GateOp → List α → α) (gs : List Gate)
    (xs : List α) (i : ℕ) (hi : i < xs.length) :
    (evalFrom d op gs xs).getD i d = xs.getD i d := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [evalFrom_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

private def row (C : Circuit) (k : Fin C.size) : Gate := C.gates[k.val]'k.isLt

private def operand (C : Circuit) (k : Fin C.size) (b : Fin 2) : ℕ :=
  (row C k).inputs.getD b.val 0

private def outWire (n : ℕ) {s : ℕ} (k : Fin s) : ℕ := n + k.val

private lemma inputs_two {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).inputs = [operand C k 0, operand C k 1] := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (h.2.2 (row C k) (List.getElem_mem _))
  simp [operand, hab]

private lemma op_kind {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    (row C k).op = GateOp.and ∨ (row C k).op = GateOp.or :=
  h.1 (row C k) (List.getElem_mem _)

private lemma earlier {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (b : Fin 2) : operand C k b < outWire n k := by
  have he : gateAt C k.val = row C k := List.getD_eq_getElem _ _ k.isLt
  have hm : operand C k b ∈ (row C k).inputs := by
    rw [inputs_two h k]
    fin_cases b <;> simp
  exact h.2.1 k.val k.isLt (operand C k b) (by simpa only [he] using hm)

private lemma evalFrom_gate {α : Type} (d : α) (op : GateOp → List α → α) {n : ℕ}
    {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (xs : List α) (hx : xs.length = n)
    (k : Fin C.size) :
    (evalFrom d op C.gates xs).getD (outWire n k) d =
      op (row C k).op ([(evalFrom d op C.gates xs).getD (operand C k 0) d,
        (evalFrom d op C.gates xs).getD (operand C k 1) d]) := by
  let front := evalFrom d op (C.gates.take k.val) xs
  have hf : front.length = outWire n k := by
    have hk : k.val ≤ C.gates.length := k.isLt.le
    simp [front, evalFrom_length, hx, outWire, Nat.min_eq_left hk]
  have hsplit : evalFrom d op C.gates xs =
      evalFrom d op (row C k :: C.gates.drop (k.val + 1)) front := by
    simp only [front, row, evalFrom, ← List.foldl_append, ← List.drop_eq_getElem_cons k.isLt,
      List.take_append_drop]
  have hread (i : ℕ) (hi : i < outWire n k) :
      (evalFrom d op C.gates xs).getD i d = front.getD i d := by
    rw [hsplit, evalFrom_input _ _ _ _ _ (by simpa only [hf] using hi)]
  change (evalFrom d op C.gates xs).getD (outWire n k) d = _
  rw [hread _ (earlier h k 0), hread _ (earlier h k 1), hsplit, evalFrom_cons]
  rw [evalFrom_input _ _ _ _ _ (by simp; omega)]
  rw [List.getD_append_right _ _ _ _ (by omega)]
  simp [hf, inputs_two h k]

private lemma wire_cases (n s w : ℕ) :
    w < n ∨ (∃ k : Fin s, w = outWire n k) ∨ n + s ≤ w := by
  by_cases hb : w < n
  · exact Or.inl hb
  by_cases he : w < n + s
  · exact Or.inr (Or.inl ⟨⟨w - n, by omega⟩, by simp [outWire]; omega⟩)
  · exact Or.inr (Or.inr (by omega))

private def wordOp : GateOp → List (Set (List ℕ)) → Set (List ℕ)
  | .or, [a, b] => a ∪ b
  | .and, [a, b] => {t | ∃ u ∈ a, ∃ v ∈ b, t = u ++ v}
  | _, _ => ∅

private def wordList (n : ℕ) (C : Circuit) : List (Set (List ℕ)) :=
  evalFrom ∅ wordOp C.gates (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ))))

private def words (n : ℕ) (C : Circuit) (w : ℕ) : Set (List ℕ) :=
  (wordList n C).getD w ∅

private lemma words_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) :
    words n C w = {[w]} := by
  unfold words wordList
  have hi : w < (List.ofFn (fun i : Fin n => ({[i.val]} : Set (List ℕ)))).length := by
    simpa using hw
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma words_missing (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.size ≤ w) :
    words n C w = ∅ :=
  List.getD_eq_default _ _ (by simpa [wordList, evalFrom_length, Circuit.size] using hw)

private lemma words_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) (k : Fin C.size) :
    words n C (outWire n k) =
      wordOp (row C k).op [words n C (operand C k 0), words n C (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private def circuitValue {n : ℕ} (C : Circuit) (z : Fin n → Bool) (w : ℕ) : Bool :=
  (evalFrom false GateOp.eval C.gates (List.ofFn z)).getD w false

private lemma value_input {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ} (hw : w < n) :
    circuitValue C z w = z ⟨w, hw⟩ := by
  have hi : w < (List.ofFn z).length := by simpa using hw
  unfold circuitValue
  rw [evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

private lemma value_missing {n : ℕ} (C : Circuit) (z : Fin n → Bool) {w : ℕ}
    (hw : n + C.size ≤ w) : circuitValue C z w = false :=
  List.getD_eq_default _ _ (by simpa [evalFrom_length, Circuit.size] using hw)

private lemma value_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (k : Fin C.size) :
    circuitValue C z (outWire n k) = (row C k).op.eval
      [circuitValue C z (operand C k 0), circuitValue C z (operand C k 1)] :=
  evalFrom_gate _ _ h _ List.length_ofFn k

private lemma value_eq_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (z : Fin n → Bool) (w : ℕ) :
    circuitValue C z w = true ↔
      ∃ t ∈ words n C w, ∀ i ∈ t, ∃ a : Fin n, a.val = i ∧ z a = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [value_input C z hb, words_input C hb]
      constructor
      · intro ht
        exact ⟨[w], rfl, fun i hi => ⟨⟨w, hb⟩, by simpa only [List.mem_singleton, eq_comm] using hi, ht⟩⟩
      · rintro ⟨t, ht, hp⟩
        have ht' : t = [w] := ht
        obtain ⟨a, ha, hz⟩ := hp w (by simp [ht'])
        exact (Fin.ext ha : a = ⟨w, hb⟩) ▸ hz
    · have h1 := ih _ (earlier h k 0)
      have h2 := ih _ (earlier h k 1)
      rw [value_gate h z k, words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho]
        simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
          Bool.and_eq_true, wordOp, Set.mem_ofPred_eq, h1, h2]
        constructor
        · rintro ⟨⟨t, ht, htz⟩, ⟨u, hu, huz⟩⟩
          exact ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, fun i hi =>
            (List.mem_append.mp hi).elim (htz i) (huz i)⟩
        · rintro ⟨_, ⟨t, ht, u, hu, rfl⟩, hh⟩
          exact ⟨⟨t, ht, fun i hi => hh i (List.mem_append_left _ hi)⟩,
            ⟨u, hu, fun i hi => hh i (List.mem_append_right _ hi)⟩⟩
      · rw [ho]
        simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
          Bool.or_eq_true, wordOp, Set.mem_union, h1, h2]
        exact ⟨fun h => h.elim (fun ⟨t, ht, ha⟩ => ⟨t, Or.inl ht, ha⟩)
          (fun ⟨t, ht, ha⟩ => ⟨t, Or.inr ht, ha⟩),
          fun ⟨t, ht, ha⟩ => ht.elim (fun h => Or.inl ⟨t, h, ha⟩) (fun h => Or.inr ⟨t, h, ha⟩)⟩
    · simp [value_missing C z hb, words_missing n C hb]

private lemma words_nonempty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w : ℕ} {t : List ℕ} (ht : t ∈ words n C w) : t ≠ [] := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · rw [words_input C hb] at ht
      have ht' : t = [w] := ht
      simp [ht']
    · rw [words_gate h k] at ht
      rcases op_kind h k with ho | ho
      · rw [ho] at ht
        obtain ⟨u, hu, v, _, rfl⟩ := ht
        exact fun hh => ih _ (earlier h k 0) hu (List.append_eq_nil_iff.mp hh).1
      · rw [ho] at ht
        exact ht.elim (ih _ (earlier h k 0)) (ih _ (earlier h k 1))
    · simp [words_missing n C hb] at ht

end Circuit

section ReadWitness

-- Decode capped multiplicities into actual words of input leaves.

open PEqualNP.CircuitLowerBounds PEqualNP.ReadK

private lemma mem_insertNew (a v : List ℕ) (A : List (List ℕ)) :
    v ∈ insertNew A a ↔ v ∈ A ∨ v = a := by
  unfold insertNew
  by_cases ha : a ∈ A
  · simp [ha, or_iff_left_of_imp (fun (e : v = a) => e.symm ▸ ha)]
  · simp [ha]

private lemma mem_fold_insertNew (v : List ℕ) (B A : List (List ℕ)) :
    v ∈ B.foldl insertNew A ↔ v ∈ A ∨ v ∈ B := by
  induction B generalizing A with
  | nil => simp
  | cons b B ih => simp [ih, mem_insertNew, or_assoc]

private lemma mem_andStep_two (v : List ℕ) (A B : List (List ℕ)) :
    v ∈ andStep 1 A B ↔ ∃ u ∈ A, ∃ w ∈ B, v = capAdd 1 u w := by
  simp [andStep, mem_fold_insertNew, List.mem_flatMap, List.mem_map, eq_comm]

private def encode (S t : List ℕ) : List ℕ :=
  S.map fun j => min (t.count j) 2

private lemma encode_nil (S : List ℕ) : encode S [] = S.map (fun _ => 0) := by
  simp [encode]

private lemma encode_append (S t u : List ℕ) :
    capAdd 1 (encode S t) (encode S u) = encode S (t ++ u) := by
  induction S with
  | nil => rfl
  | cons a S ih =>
    simp only [encode, capAdd, List.map_cons, List.zipWith_cons_cons, List.count_append] at ih ⊢
    rw [ih]
    congr 1
    omega

private def readOp (S : List ℕ) (o : GateOp) (ins : List (List (List ℕ))) : List (List ℕ) :=
  match o with
  | .or => ins.foldl (fun acc A => A.foldl insertNew acc) []
  | .and => ins.foldl (andStep 1) [S.map fun _ => 0]
  | _ => []

private def vecs (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) : List (List ℕ) :=
  ((readVectors C n S 1).getD w [])

private lemma vec_eval (n : ℕ) (C : Circuit) (S : List ℕ) (w : ℕ) :
    vecs n C S w =
      (evalFrom [] (readOp S) C.gates ((List.range n).map (leafVectors S 1))).getD w [] :=
  rfl

private lemma encode_witness {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (w : ℕ) (v : List ℕ) (hv : v ∈ vecs n C S w) :
    ∃ t ∈ words n C w, v = encode S t ∧ ∀ i ∈ t, i ∈ S := by
  induction w using Nat.strong_induction_on generalizing v with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨k, rfl⟩ | hb
    · have hi : w < ((List.range n).map (leafVectors S 1)).length := by simpa using hb
      rw [vec_eval, evalFrom_input _ _ _ _ _ hi, List.getD_eq_getElem _ _ hi] at hv
      simp only [List.getElem_map, List.getElem_range] at hv
      rw [words_input C hb]
      by_cases hs : w ∈ S
      · refine ⟨[w], rfl, ?_, by simpa using hs⟩
        have hvec : v = S.map (fun j => if j = w then min 1 (1 + 1) else 0) := by
          simpa only [leafVectors, hs, ite_true, List.mem_singleton] using hv
        rw [hvec]
        unfold encode
        apply List.map_congr_left
        intro a _
        by_cases hea : a = w
        · simp [hea]
        · simp [hea, Ne.symm hea]
      · simp [leafVectors, hs] at hv
    · have hlen : ((List.range n).map (leafVectors S 1)).length = n := by simp
      have hvec := evalFrom_gate ([] : List (List ℕ)) (readOp S) h _ hlen k
      rw [← vec_eval, ← vec_eval, ← vec_eval] at hvec
      rw [hvec] at hv
      rw [words_gate h k]
      rcases op_kind h k with ho | ho
      · rw [ho] at hv ⊢
        change v ∈ andStep 1 (andStep 1 [S.map (fun _ => 0)] (vecs n C S (operand C k 0)))
          (vecs n C S (operand C k 1)) at hv
        obtain ⟨x, hx, y, hy, rfl⟩ := (mem_andStep_two _ _ _).mp hv
        obtain ⟨z, hz, x', hx', rfl⟩ := (mem_andStep_two _ _ _).mp hx
        obtain ⟨t, ht, rfl, hts⟩ := ih _ (earlier h k 0) _ hx'
        obtain ⟨u, hu, rfl, hus⟩ := ih _ (earlier h k 1) _ hy
        refine ⟨t ++ u, ⟨t, ht, u, hu, rfl⟩, ?_, fun i hi =>
          (List.mem_append.mp hi).elim (hts i) (hus i)⟩
        have hz' : z = encode S [] := by simpa [encode_nil] using hz
        rw [hz', encode_append, List.nil_append, encode_append]
      · rw [ho] at hv ⊢
        change v ∈ (vecs n C S (operand C k 1)).foldl insertNew
          ((vecs n C S (operand C k 0)).foldl insertNew []) at hv
        rw [mem_fold_insertNew, mem_fold_insertNew] at hv
        simp only [List.not_mem_nil, false_or] at hv
        rcases hv with hp | hp
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 0) _ hp
          exact ⟨t, Or.inl ht, he, hs⟩
        · obtain ⟨t, ht, he, hs⟩ := ih _ (earlier h k 1) _ hp
          exact ⟨t, Or.inr ht, he, hs⟩
    · rw [vec_eval, List.getD_eq_default _ _ (by
        simpa [evalFrom_length, Circuit.size] using hb)] at hv
      simp at hv

private lemma read_to_terms {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (S : List ℕ) (r : readsAtMost C n S 1 = true) :
    ∃ t ∈ words n C C.output, (∀ i ∈ t, i ∈ S) ∧ ∀ i ∈ S, t.count i ≤ 1 := by
  obtain ⟨v, hv, ha⟩ := List.any_eq_true.mp r
  obtain ⟨t, ht, rfl, hts⟩ := encode_witness h S C.output v hv
  refine ⟨t, ht, hts, fun i hi => ?_⟩
  have hv : min (t.count i) 2 ∈ encode S t := List.mem_map.mpr ⟨i, hi, rfl⟩
  have hb := of_decide_eq_true ((List.all_eq_true.mp ha) _ hv)
  omega

end ReadWitness


def OrStep (n : ℕ) (C : Circuit) (w v : ℕ) : Prop :=
  ∃ k : Fin C.size, w = outWire n k ∧ (row C k).op = GateOp.or ∧ v ∈ (row C k).inputs

abbrev OrPath (n : ℕ) (C : Circuit) := Relation.ReflTransGen (OrStep n C)

noncomputable def singles (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun a => [a.val] ∈ words n C w)

lemma mem_singles {n : ℕ} {C : Circuit} {w : ℕ} {a : Fin n} :
    a ∈ singles n C w ↔ [a.val] ∈ words n C w := by
  classical
  simp [singles]

lemma pair_word_gate {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (w : ℕ) (t : List ℕ) (ht : t ∈ words n C w) (hlen : t.length = 2) :
    ∃ k : Fin C.size, (row C k).op = GateOp.and ∧ OrPath n C w (outWire n k) ∧
      ∃ a b : ℕ, t = [a,b] ∧ [a] ∈ words n C (operand C k 0) ∧
        [b] ∈ words n C (operand C k 1) := by
  induction w using Nat.strong_induction_on generalizing t with
  | ind w ih =>
    rcases wire_cases n C.size w with hb | ⟨j,rfl⟩ | hb
    · rw [words_input C hb] at ht
      have he : t = [w] := ht
      simp [he] at hlen
    · rw [words_gate h j] at ht
      rcases op_kind h j with ho | ho
      · rw [ho] at ht
        obtain ⟨u,hu,v,hv,rfl⟩ := ht
        have hupos : 0 < u.length := List.length_pos_iff.mpr (words_nonempty h hu)
        have hvpos : 0 < v.length := List.length_pos_iff.mpr (words_nonempty h hv)
        have hsum : u.length + v.length = 2 := by simpa using hlen
        obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp (by omega : u.length = 1)
        obtain ⟨b,rfl⟩ := List.length_eq_one_iff.mp (by omega : v.length = 1)
        exact ⟨j,ho,Relation.ReflTransGen.refl,a,b,rfl,hu,hv⟩
      · rw [ho] at ht
        change t ∈ words n C (operand C j 0) ∪ words n C (operand C j 1) at ht
        rcases ht with ht | ht
        · obtain ⟨k,hk,hp,a,b,he,ha,hb⟩ := ih _ (earlier h j 0) t ht hlen
          refine ⟨k,hk,Relation.ReflTransGen.head ?_ hp,a,b,he,ha,hb⟩
          exact ⟨j,rfl,ho,by rw [inputs_two h j]; simp⟩
        · obtain ⟨k,hk,hp,a,b,he,ha,hb⟩ := ih _ (earlier h j 1) t ht hlen
          refine ⟨k,hk,Relation.ReflTransGen.head ?_ hp,a,b,he,ha,hb⟩
          exact ⟨j,rfl,ho,by rw [inputs_two h j]; simp⟩
    · simp [words_missing n C hb] at ht

lemma read_pair_word {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (singleFalse : ∀ a : Fin n, circuitFun n C (fun k => decide (k=a)) = false)
    (a b : Fin n) (hab : a ≠ b)
    (hr : PEqualNP.ReadK.readsAtMost C n [a.val,b.val] 1 = true) :
    ∃ t ∈ words n C C.output, t.length = 2 ∧ t.Nodup ∧ ∀ i ∈ t, i ∈ [a.val,b.val] := by
  classical
  obtain ⟨t,ht,hs,hcount⟩ := read_to_terms h [a.val,b.val] hr
  have hn : t.Nodup := List.nodup_iff_count_le_one.mpr (by
    intro i
    by_cases hi : i ∈ t
    · exact hcount i (hs i hi)
    · simp [List.count_eq_zero.mpr hi])
  have hsub : t.toFinset ⊆ ({a.val,b.val} : Finset ℕ) := by
    intro i hi
    have hm := hs i (List.mem_toFinset.mp hi)
    simpa using hm
  have habv : a.val ≠ b.val := fun he => hab (Fin.ext he)
  have hcard : t.toFinset.card ≤ 2 := by
    have hc := Finset.card_le_card hsub
    simpa [habv] using hc
  rw [List.toFinset_card_of_nodup hn] at hcard
  have hpos : 0 < t.length := List.length_pos_iff.mpr (words_nonempty h ht)
  have hnotone : t.length ≠ 1 := by
    intro hone
    obtain ⟨i,he⟩ := List.length_eq_one_iff.mp hone
    subst t
    have hi := hs i (by simp)
    obtain ⟨z,hz⟩ : ∃ z : Fin n, z.val = i := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with hi | hi
      · exact ⟨a,hi.symm⟩
      · exact ⟨b,hi.symm⟩
    have hv : circuitFun n C (fun k => decide (k=z)) = true := by
      change circuitValue C (fun k => decide (k=z)) C.output = true
      apply (value_eq_terms h _ _).2
      refine ⟨[i],ht,?_⟩
      intro j hj
      have hj' : j=i := by simpa using hj
      exact ⟨z,hz.trans hj'.symm,by simp⟩
    rw [singleFalse z] at hv
    cases hv
  exact ⟨t,ht,by omega,hn,hs⟩


lemma row_gateAt (C : Circuit) (k : Fin C.size) : gateAt C k.val = row C k :=
  List.getD_eq_getElem _ _ k.isLt

lemma step_lt {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w v : ℕ} (hs : OrStep n C w v) : v < w := by
  obtain ⟨k,rfl,_,hv⟩ := hs
  exact h.2.1 k.val k.isLt v (by simpa only [row_gateAt C k] using hv)

lemma path_le {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w v : ℕ} (hp : OrPath n C w v) : v ≤ w := by
  induction hp with
  | refl => exact le_rfl
  | tail hp hs ih => exact (step_lt h hs).le.trans ih

lemma step_word_up {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w v : ℕ} (hs : OrStep n C w v) (t : List ℕ) (ht : t ∈ words n C v) :
    t ∈ words n C w := by
  obtain ⟨k,rfl,ho,hv⟩ := hs
  rw [inputs_two h k] at hv
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
  rw [words_gate h k,ho]
  rcases hv with rfl | rfl
  · exact Or.inl ht
  · exact Or.inr ht

lemma path_word_up {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {w v : ℕ} (hp : OrPath n C w v) :
    ∀ t : List ℕ, t ∈ words n C v → t ∈ words n C w := by
  induction hp with
  | refl => exact fun _ ht => ht
  | tail hp hs ih => exact fun t ht => ih t (step_word_up h hs t ht)

lemma single_word_value {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (a : Fin n) (w : ℕ) (ht : [a.val] ∈ words n C w) :
    circuitValue C (fun k => decide (k=a)) w = true := by
  apply (value_eq_terms h _ _).2
  refine ⟨[a.val],ht,?_⟩
  intro i hi
  have he : i=a.val := by simpa using hi
  exact ⟨a,he.symm,by simp⟩

lemma singles_empty_path {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (singleFalse : ∀ a : Fin n, circuitFun n C (fun k => decide (k=a)) = false)
    {w : ℕ} (hp : OrPath n C C.output w) : singles n C w = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have hv := single_word_value h a C.output (path_word_up h hp _ (mem_singles.mp ha))
  change circuitFun n C (fun k => decide (k=a)) = true at hv
  rw [singleFalse a] at hv
  cases hv

lemma singles_and_empty {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (ho : (row C k).op = GateOp.and) :
    singles n C (outWire n k) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have ht := mem_singles.mp ha
  rw [words_gate h k,ho] at ht
  obtain ⟨u,hu,v,hv,he⟩ := ht
  have hupos := List.length_pos_iff.mpr (words_nonempty h hu)
  have hvpos := List.length_pos_iff.mpr (words_nonempty h hv)
  have hlen := congrArg List.length he
  simp only [List.length_cons,List.length_nil,List.length_append] at hlen
  omega

lemma singles_input_card (n : ℕ) (C : Circuit) (w : ℕ) (hw : w<n) :
    (singles n C w).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro a ha b hb
  have he1 : a.val=w := by simpa [words_input C hw] using mem_singles.mp ha
  have he2 : b.val=w := by simpa [words_input C hw] using mem_singles.mp hb
  exact Fin.ext (he1.trans he2.symm)

lemma singles_or {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (k : Fin C.size) (ho : (row C k).op = GateOp.or) (a : Fin n) :
    a ∈ singles n C (outWire n k) ↔
      ∃ w ∈ (row C k).inputs, a ∈ singles n C w := by
  rw [mem_singles,words_gate h k,ho]
  change ([a.val] ∈ words n C (operand C k 0) ∨
    [a.val] ∈ words n C (operand C k 1)) ↔ _
  rw [inputs_two h k]
  simp [mem_singles]


lemma gate_default {C : Circuit} {k : ℕ} (hk : C.size ≤ k) :
    gateAt C k = ⟨GateOp.or,[]⟩ := by
  simp [gateAt,List.getD_eq_getElem?_getD,List.getElem?_eq_none hk]

lemma total_back {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    ∀ k, ∀ i ∈ (gateAt C k).inputs, i < n+k := by
  intro k i hi
  by_cases hk : k<C.size
  · exact h.2.1 k hk i hi
  · rw [gate_default (by omega)] at hi
    simp at hi

lemma singles_missing {n : ℕ} (C : Circuit) (w : ℕ) (hw : n+C.size ≤ w) :
    singles n C w = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have ht := mem_singles.mp ha
  simp [words_missing n C hw] at ht

lemma total_or {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    ∀ k, (gateAt C k).op = GateOp.or → ∀ a,
      a ∈ singles n C (n+k) ↔ ∃ w ∈ (gateAt C k).inputs, a ∈ singles n C w := by
  intro k ho a
  by_cases hk : k<C.size
  · have he := row_gateAt C ⟨k,hk⟩
    simpa [outWire,he] using singles_or h ⟨k,hk⟩ (by simpa [he] using ho) a
  · rw [gate_default (by omega),singles_missing C _ (by omega)]
    simp

lemma total_nonor {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    ∀ k, (gateAt C k).op ≠ GateOp.or → (singles n C (n+k)).card ≤ 1 := by
  intro k ho
  by_cases hk : k<C.size
  · have he := row_gateAt C ⟨k,hk⟩
    have ha : (row C ⟨k,hk⟩).op = GateOp.and :=
      (op_kind h ⟨k,hk⟩).resolve_right (by simpa [he] using ho)
    have hz := singles_and_empty h ⟨k,hk⟩ ha
    change singles n C (n+k) = ∅ at hz
    rw [hz]
    simp
  · exact False.elim (ho (by rw [gate_default (by omega)]))

lemma pair_word_value {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (a b : Fin n) (w : ℕ) (ht : [a.val,b.val] ∈ words n C w) :
    circuitValue C (fun k => decide (k=a ∨ k=b)) w = true := by
  apply (value_eq_terms h _ _).2
  refine ⟨[a.val,b.val],ht,?_⟩
  intro i hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl
  · exact ⟨a,rfl,by simp⟩
  · exact ⟨b,rfl,by simp⟩

lemma cross_adj {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 n C)
    (singleFalse : ∀ a : Fin n, circuitFun n C (fun k => decide (k=a)) = false)
    (pairFalse : ∀ a b : Fin n, a≠b → ¬G.Adj a b →
      circuitFun n C (fun k => decide (k=a ∨ k=b)) = false)
    (j : Fin C.size) (ho : (row C j).op = GateOp.and)
    (hp : OrPath n C C.output (outWire n j))
    (a b : Fin n) (ha : a ∈ singles n C (operand C j 0))
    (hb : b ∈ singles n C (operand C j 1)) : G.Adj a b := by
  have ht : [a.val,b.val] ∈ words n C (outWire n j) := by
    rw [words_gate h j,ho]
    exact ⟨[a.val],mem_singles.mp ha,[b.val],mem_singles.mp hb,rfl⟩
  have hv := pair_word_value h a b C.output (path_word_up h hp _ ht)
  change circuitFun n C (fun k => decide (k=a ∨ k=b)) = true at hv
  by_cases hab : a=b
  · subst b
    have hv' : circuitFun n C (fun k => decide (k=a)) = true := by simpa using hv
    rw [singleFalse a] at hv'
    cases hv'
  · by_contra hn
    rw [pairFalse a b hab hn] at hv
    cases hv

lemma cross_star {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (h4 : PEqualNP.TopForm.NoFourCycle G)
    (L R : Finset (Fin n)) (hc : ∀ a∈L, ∀ b∈R, G.Adj a b) :
    L.card ≤ 1 ∨ R.card ≤ 1 := by
  by_cases hl : L.card ≤ 1
  · exact Or.inl hl
  · right
    by_contra hr
    obtain ⟨a,ha,c,hc',hac⟩ := Finset.one_lt_card.mp (by omega : 1<L.card)
    obtain ⟨b,hb,d,hd,hbd⟩ := Finset.one_lt_card.mp (by omega : 1<R.card)
    have hcommon := h4 a c hac
    have hmem (v : Fin n) (hv : v∈R) :
        v ∈ Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      simp [hc a ha v hv,hc c hc' v hv]
    have htwo := Finset.one_lt_card.mpr ⟨b,hmem b hb,d,hmem d hd,hbd⟩
    omega


lemma opnd_row (C : Circuit) (k : Fin C.size) (b : Fin 2) :
    PEqualNP.TopForm.opnd C k.val b = operand C k b := by
  simp [PEqualNP.TopForm.opnd,row_gateAt,operand]

noncomputable def J (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter (fun j =>
    (gateAt C j).op = GateOp.and ∧ OrPath n C C.output (n+j) ∧
      (singles n C (PEqualNP.TopForm.opnd C j 0)).Nonempty ∧
      (singles n C (PEqualNP.TopForm.opnd C j 1)).Nonempty)

noncomputable def D (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.size).filter (fun j =>
    (gateAt C j).op = GateOp.or ∧ OrPath n C C.output (n+j))

lemma mem_J {n : ℕ} {C : Circuit} {j : ℕ} :
    j ∈ J n C ↔ j<C.size ∧ (gateAt C j).op=GateOp.and ∧
      OrPath n C C.output (n+j) ∧
      (singles n C (PEqualNP.TopForm.opnd C j 0)).Nonempty ∧
      (singles n C (PEqualNP.TopForm.opnd C j 1)).Nonempty := by
  classical
  simp [J]

lemma mem_D {n : ℕ} {C : Circuit} {j : ℕ} :
    j ∈ D n C ↔ j<C.size ∧ (gateAt C j).op=GateOp.or ∧
      OrPath n C C.output (n+j) := by
  classical
  simp [D]

lemma J_star {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (h : PEqualNP.TopForm.IsAO2 n C) (h4 : PEqualNP.TopForm.NoFourCycle G)
    (hs : ∀ a : Fin n, circuitFun n C (fun k => decide (k=a)) = false)
    (hf : ∀ a b : Fin n, a≠b → ¬G.Adj a b →
      circuitFun n C (fun k => decide (k=a ∨ k=b)) = false)
    (j : ℕ) (hj : j ∈ J n C) :
    (∀ a∈singles n C (PEqualNP.TopForm.opnd C j 0),
      ∀ b∈singles n C (PEqualNP.TopForm.opnd C j 1), G.Adj a b) ∧
    ((singles n C (PEqualNP.TopForm.opnd C j 0)).card ≤ 1 ∨
      (singles n C (PEqualNP.TopForm.opnd C j 1)).card ≤ 1) := by
  obtain ⟨hn,ho,hp,hL,hR⟩ := mem_J.mp hj
  have hc : ∀ a∈singles n C (PEqualNP.TopForm.opnd C j 0),
      ∀ b∈singles n C (PEqualNP.TopForm.opnd C j 1), G.Adj a b := by
    intro a ha b hb
    exact cross_adj h hs hf ⟨j,hn⟩ (by rw [← row_gateAt C ⟨j,hn⟩]; exact ho) hp a b
      (by rw [← opnd_row C ⟨j,hn⟩ 0]; exact ha)
      (by rw [← opnd_row C ⟨j,hn⟩ 1]; exact hb)
  exact ⟨hc,cross_star h4 _ _ hc⟩

lemma read_pair_join {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    (hs : ∀ a : Fin n, circuitFun n C (fun k => decide (k=a)) = false)
    (a b : Fin n) (hab : a≠b)
    (hr : PEqualNP.ReadK.readsAtMost C n [a.val,b.val] 1 = true) :
    ∃ j∈J n C,
      (a ∈ singles n C (PEqualNP.TopForm.opnd C j 0) ∧
        b ∈ singles n C (PEqualNP.TopForm.opnd C j 1)) ∨
      (b ∈ singles n C (PEqualNP.TopForm.opnd C j 0) ∧
        a ∈ singles n C (PEqualNP.TopForm.opnd C j 1)) := by
  obtain ⟨t,ht,hlen,hnd,hsub⟩ := read_pair_word h hs a b hab hr
  obtain ⟨k,ho,hp,u,v,he,hu,hv⟩ := pair_word_gate h C.output t ht hlen
  have hunev : u≠v := by
    intro huv
    rw [he,huv] at hnd
    simp at hnd
  have hus := hsub u (by rw [he]; simp)
  have hvs := hsub v (by rw [he]; simp)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hus hvs
  obtain ⟨p,hpu⟩ : ∃ p : Fin n, p.val=u := by
    rcases hus with h | h
    · exact ⟨a,h.symm⟩
    · exact ⟨b,h.symm⟩
  obtain ⟨q,hqv⟩ : ∃ q : Fin n, q.val=v := by
    rcases hvs with h | h
    · exact ⟨a,h.symm⟩
    · exact ⟨b,h.symm⟩
  have hpm : p ∈ singles n C (PEqualNP.TopForm.opnd C k.val 0) := by
    rw [opnd_row,mem_singles,hpu]
    exact hu
  have hqm : q ∈ singles n C (PEqualNP.TopForm.opnd C k.val 1) := by
    rw [opnd_row,mem_singles,hqv]
    exact hv
  refine ⟨k.val,mem_J.mpr ⟨k.isLt,by simpa [row_gateAt] using ho,hp,
    ⟨p,hpm⟩,⟨q,hqm⟩⟩,?_⟩
  have hpa : p=a ∨ p=b := hus.imp (fun e => Fin.ext (hpu.trans e)) (fun e => Fin.ext (hpu.trans e))
  have hqa : q=a ∨ q=b := hvs.imp (fun e => Fin.ext (hqv.trans e)) (fun e => Fin.ext (hqv.trans e))
  rcases hpa with rfl | rfl <;> rcases hqa with rfl | rfl
  · exact False.elim (hunev (hpu.symm.trans hqv))
  · exact Or.inl ⟨hpm,hqm⟩
  · exact Or.inr ⟨hpm,hqm⟩
  · exact False.elim (hunev (hpu.symm.trans hqv))


lemma J_disjoint_D (n : ℕ) (C : Circuit) : Disjoint (J n C) (D n C) := by
  classical
  apply Finset.disjoint_left.mpr
  intro j hj hd
  have ha := (mem_J.mp hj).2.1
  have ho := (mem_D.mp hd).2.1
  cases ha.symm.trans ho

lemma or_length {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    ∀ j, (gateAt C j).op=GateOp.or → (gateAt C j).inputs.length ≤ 2 := by
  intro j _
  by_cases hj : j<C.size
  · rw [row_gateAt C ⟨j,hj⟩]
    exact (h.2.2 _ (List.getElem_mem hj)).le
  · rw [gate_default (by omega)]
    simp

lemma J_card_le_D {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C) :
    (J n C).card ≤ (D n C).card+1 := by
  classical
  let U : Finset ℕ := insert C.output ((D n C).biUnion (fun j => (gateAt C j).inputs.toFinset))
  have hp_mem {w : ℕ} (hp : OrPath n C C.output w) : w∈U := by
    rcases Relation.ReflTransGen.cases_tail hp with he | ⟨v,hpv,hs⟩
    · rw [he]
      exact Finset.mem_insert_self _ _
    · obtain ⟨k,he,ho,hw⟩ := hs
      have hk : k.val ∈ D n C := mem_D.mpr ⟨k.isLt,
        by rw [row_gateAt]; exact ho,
        by simpa [outWire,he] using hpv⟩
      apply Finset.mem_insert_of_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨k.val,hk,?_⟩
      rw [row_gateAt]
      exact List.mem_toFinset.mpr hw
  have hsub : ((J n C ∪ D n C).image (fun j => n+j)) ⊆ U := by
    intro w hw
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hw
    rcases Finset.mem_union.mp hj with hj | hj
    · exact hp_mem (mem_J.mp hj).2.2.1
    · exact hp_mem (mem_D.mp hj).2.2
  have hlow : (J n C).card + (D n C).card ≤ U.card := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ (fun _ _ he => Nat.add_left_cancel he),
      Finset.card_union_of_disjoint (J_disjoint_D n C)] at hc
    exact hc
  have hsz : ∀ j∈D n C, (gateAt C j).inputs.toFinset.card ≤ 2 := by
    intro j hj
    exact (List.toFinset_card_le _).trans (or_length h j (mem_D.mp hj).2.1)
  have hup : U.card ≤ 2*(D n C).card+1 := by
    calc
      U.card ≤ ((D n C).biUnion (fun j => (gateAt C j).inputs.toFinset)).card+1 :=
        Finset.card_insert_le _ _
      _ ≤ (∑ j∈D n C, (gateAt C j).inputs.toFinset.card)+1 :=
        Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ (∑ _j∈D n C, 2)+1 := Nat.add_le_add_right (Finset.sum_le_sum hsz) _
      _ = 2*(D n C).card+1 := by simp [Nat.mul_comm]
  omega

lemma raw_path_le {n : ℕ} {C : Circuit} (h : PEqualNP.TopForm.IsAO2 n C)
    {i j : ℕ} (hp : Relation.ReflTransGen
      (fun i j => (gateAt C i).op = GateOp.or ∧ n + j ∈ (gateAt C i).inputs) i j) : j ≤ i := by
  induction hp with
  | refl => exact le_rfl
  | tail hp hs ih =>
    have hl := total_back h _ _ hs.2
    omega

noncomputable def centre (n : ℕ) (C : Circuit) (v0 : Fin n) (j : ℕ) : Fin n :=
  if (singles n C (PEqualNP.TopForm.opnd C j 0)).card ≤ 1 then
    if h : (singles n C (PEqualNP.TopForm.opnd C j 0)).Nonempty then h.choose else v0
  else
    if h : (singles n C (PEqualNP.TopForm.opnd C j 1)).Nonempty then h.choose else v0

lemma centre_cross (n : ℕ) (C : Circuit) (v0 : Fin n) (j : ℕ)
    (hL : (singles n C (PEqualNP.TopForm.opnd C j 0)).Nonempty)
    (hR : (singles n C (PEqualNP.TopForm.opnd C j 1)).Nonempty)
    (hstar : (singles n C (PEqualNP.TopForm.opnd C j 0)).card ≤ 1 ∨
      (singles n C (PEqualNP.TopForm.opnd C j 1)).card ≤ 1)
    (a b : Fin n) (ha : a∈singles n C (PEqualNP.TopForm.opnd C j 0))
    (hb : b∈singles n C (PEqualNP.TopForm.opnd C j 1)) :
    centre n C v0 j=a ∨ centre n C v0 j=b := by
  classical
  by_cases hc : (singles n C (PEqualNP.TopForm.opnd C j 0)).card ≤ 1
  · left
    rw [centre,if_pos hc,dif_pos hL]
    exact Finset.card_le_one.mp hc _ hL.choose_spec _ ha
  · right
    have hr := hstar.resolve_left hc
    rw [centre,if_neg hc,dif_pos hR]
    exact Finset.card_le_one.mp hr _ hR.choose_spec _ hb

end Tree

namespace Counting
theorem cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
    f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (g k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩

theorem cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
    (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
    (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
  classical
  refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
  intro u v huv
  obtain ⟨a, ha, h | h⟩ := hcov u v huv
  · left
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
  · right
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha

theorem four_split (N : ℕ) (isAnd isOr bel : ℕ → Prop)
    (hAO : ∀ k, k < N → (isAnd k ∧ ¬ isOr k) ∨ (isOr k ∧ ¬ isAnd k))
    (T J O Q : Finset ℕ)
    (hT : ∀ k, k ∈ T ↔ k < N ∧ isAnd k ∧ bel k)
    (hJ : ∀ k, k ∈ J ↔ k < N ∧ isAnd k ∧ ¬ bel k)
    (hO : ∀ k, k ∈ O ↔ k < N ∧ isOr k ∧ bel k)
    (hQ : ∀ k, k ∈ Q ↔ k < N ∧ isOr k ∧ ¬ bel k) :
    T.card + J.card + O.card + Q.card = N := by
  classical
  have h1 : Disjoint T J := by
    rw [Finset.disjoint_left]
    intro k h h'
    exact ((hJ k).1 h').2.2 ((hT k).1 h).2.2
  have h2 : Disjoint (T ∪ J) O := by
    rw [Finset.disjoint_left]
    intro k h h'
    have ho := (hO k).1 h'
    rcases hAO k ho.1 with ha | ha
    · exact ha.2 ho.2.1
    · rcases Finset.mem_union.1 h with h | h
      · exact ha.2 ((hT k).1 h).2.1
      · exact ha.2 ((hJ k).1 h).2.1
  have h3 : Disjoint (T ∪ J ∪ O) Q := by
    rw [Finset.disjoint_left]
    intro k h h'
    have hq := (hQ k).1 h'
    rcases Finset.mem_union.1 h with h | h
    · rcases hAO k hq.1 with ha | ha
      · exact ha.2 hq.2.1
      · rcases Finset.mem_union.1 h with h | h
        · exact ha.2 ((hT k).1 h).2.1
        · exact ha.2 ((hJ k).1 h).2.1
    · exact hq.2.2 ((hO k).1 h).2.2
  have h4 : T ∪ J ∪ O ∪ Q = Finset.range N := by
    ext k
    simp only [Finset.mem_union, Finset.mem_range, hT, hJ, hO, hQ]
    constructor
    · rintro (((h | h) | h) | h) <;> exact h.1
    · intro hk
      by_cases hb : bel k
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inl ⟨hk, ha.1, hb⟩))
        · exact Or.inl (Or.inr ⟨hk, ha.1, hb⟩)
      · rcases hAO k hk with ha | ha
        · exact Or.inl (Or.inl (Or.inr ⟨hk, ha.1, hb⟩))
        · exact Or.inr ⟨hk, ha.1, hb⟩
  have h5 := congrArg Finset.card h4
  rw [Finset.card_union_of_disjoint h3, Finset.card_union_of_disjoint h2,
    Finset.card_union_of_disjoint h1, Finset.card_range] at h5
  exact h5

def TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
  ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty

theorem cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
    (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
    with hN
  set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
  set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
  set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
  have hE2I : E2 ⊆ I := by
    intro k hk
    simp only [hE2, hE, Finset.mem_filter] at hk
    obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
    apply hI k hkR hkZ hor
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
    simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
    exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
  have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
      (if (f (n + k)).Nonempty then 1 else 0) := by
    intro k hk
    simp only [hE, Finset.mem_filter] at hk
    have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
    have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
      intro h1
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
      simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
      obtain ⟨u, hu⟩ := hw.2
      exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
    rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
    · omega
    · rw [if_pos (hne h0)]
      split_ifs <;> omega
  have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
    calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
      _ = E2.card + Ene.card := by
        rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
  have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
    have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
    omega
  have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
    rintro w hw (h | ⟨k', hk', hin⟩)
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
      simp only [hN, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hin, hw⟩
  have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · left
      rw [h]
    · right
      refine ⟨b, ?_, hb3⟩
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
  have hS2card : S2.card = Ene.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [Finset.mem_filter] at hw
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
    rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.1.2.1 h3
      · exact h3 hk.1.2.2
  have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Finset.mem_filter] at hw
      rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rw [Nat.add_sub_cancel' h1] at this
        exact hmem w hw.2 this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
      exact hmem _ hk.2 (hRU k hk.1.1)
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hE2I
  omega

theorem top_step2 (n : ℕ) (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
    (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
      (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
    ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
      (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
      (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
  classical
  by_cases hρ : ρ < n
  · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
    calc (((f ρ).image (fun v => s(c, v))) \ E0).card
        ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (f ρ).card := Finset.card_image_le
      _ ≤ 1 := hf1 ρ hρ
      _ ≤ (∅ : Finset ℕ).card + 1 := by simp
  · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
    obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
    have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
      intro k h
      induction h with
      | refl => exact le_refl _
      | tail _ hbc ih =>
        have := hback _ _ hbc.2.2
        omega
    set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
      Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
    have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
      intro k
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
    set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
    have hstops : ∀ w, w ∈ stops ↔
        (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
        (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
      intro w
      rw [hsdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
        · omega
        · have := hle _ ((hR _).1 h2)
          omega
    set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
      with hZn
    obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
    have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
      cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
        intro k hk hkZ hor htwo
        rw [hZn, Finset.mem_filter]
        exact ⟨hk, hkZ, hor, htwo⟩)
    refine ⟨Znew, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk2
      rw [hZn, Finset.mem_filter] at hk2
      exact hk2.2.1 hk
    · intro k hk
      rw [hZn, Finset.mem_filter] at hk
      refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
      rw [Nat.add_sub_cancel_left]
      have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
          Relation.ReflTransGen (fun k k' : ℕ =>
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
        intro k h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail hbc.2
      exact hreach k ((hR k).1 hk.1)
    · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
          (stops.filter (fun w => (f w).Nonempty)).biUnion
            (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
        intro e he
        rw [Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
        obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
        refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
      have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
          (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
        intro w hw'
        have hw := (Finset.mem_filter.1 hw').1
        have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
            ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
          (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
        rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
        · exact himg _ (hf1 w hwn)
        · have hweq : n + (w - n) = w := by omega
          rcases hw2 with hz | hnor
          · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
            rcases hZ _ hz hsubw with hall | hc1
            · rw [hweq] at hall
              have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                rw [Finset.sdiff_eq_empty_iff_subset]
                intro e he
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                exact hall v hv
              rw [hempty]
              simp
            · rw [hweq] at hc1
              exact himg _ hc1
          · have := hf3 _ hnor
            rw [hweq] at this
            exact himg _ this
      calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
          ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
              (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
            Finset.card_le_card hsub
        _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
            Finset.card_biUnion_le_card_mul _ _ _ hone
        _ ≤ Znew.card + 1 := by omega

theorem star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (l : List (Fin n × ℕ))
    (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
    ∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
      (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
        ≤ l.length + Z.card := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
    obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
      intro k hk hsub
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
        by_cases hc : q.1 = p.1
        · left
          intro v hv
          rw [hE0]
          refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
          rw [← hc]
          exact Finset.mem_image_of_mem _ (hfq hv)
        · right
          by_contra hcard
          have h2 : 1 < (f (n + k)).card := by omega
          obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
          have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
          have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
          have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
          have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
          exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
      · exact Or.inr (hB k hk))
    have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
    refine ⟨Z ∪ Znew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
        exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
      · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
        refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
        intro hkB
        exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
    · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
        List.length_cons, ← hE0]
      have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
          (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
        rw [Finset.sdiff_union_self_eq_union]
      have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
      rw [← hsplit] at hle
      omega

theorem assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
    (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
      ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
    (Es : Finset (Sym2 (Fin n)))
    (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
    (∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
        n ≤ o a b ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
        f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
      Es.card ≤ T.card + Z.card) ∧
    ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
      (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
  classical
  by_cases hEe : Es = ∅
  · subst hEe
    refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
    intro H K hH hK
    have h0 := hK.2 ∅ (by
      intro u v huv
      exact absurd (hH u v huv) (Finset.notMem_empty _))
    simp only [Finset.card_empty] at h0
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
    obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
    set c : ℕ → Fin n := fun a =>
      if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
      else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
    set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
    have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
        (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
      intro a ha u hu v hv
      by_cases h0 : (f (o a 0)).card ≤ 1
      · left
        have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
        · simp only [hρ, h0, ↓reduceIte]
          exact hv
      · right
        have h1 : (f (o a 1)).card ≤ 1 := by
          rcases (hstar a ha).2 with h | h
          · exact absurd h h0
          · exact h
        have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
        · simp only [hρ, h0, ↓reduceIte]
          exact hu
    set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
      with hT'
    have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
      intro a ha' v hv
      have ha := hT'T a ha'
      have hnn := (Finset.mem_filter.1 ha').2
      by_cases h0 : (f (o a 0)).card ≤ 1
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.1
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact (hstar a ha).1 _ hne.choose_spec v hv
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.2
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
    have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
      intro e he
      obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
      have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
      rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', v, h2, by rw [h1]⟩
      · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
        (T'.toList.map (fun a => (c a, ρ a))) (by
          intro p hp v hv
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
          exact hadjc a (Finset.mem_toList.1 ha) v hv)
      refine ⟨Z, ?_, ?_⟩
      · intro k hk
        obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
        have ha' := Finset.mem_toList.1 ha
        have hnn := (Finset.mem_filter.1 ha').2
        refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
        by_cases h0 : (f (o a 0)).card ≤ 1
        · refine ⟨1, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 1 : Fin 2) = 0 := by decide
          rw [e]
          exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
        · refine ⟨0, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 0 : Fin 2) = 1 := by decide
          rw [e]
          have h1' : (f (o a 1)).card ≤ 1 := by
            rcases (hstar a (hT'T a ha')).2 with h | h
            · exact absurd h h0
            · exact h
          exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
      · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
            (fun p => (f p.2).image (fun v => s(p.1, v))) := by
          intro e he
          obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
          refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
        have h1 := Finset.card_le_card hsub
        rw [List.length_map, Finset.length_toList] at hZ2
        omega
    · intro H K hH hK
      refine (cover_bound n H T' c ?_ K hK).trans hT'card
      intro u v huv
      obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
      refine ⟨a, ha, ?_⟩
      have := Sym2.eq_iff.1 he
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm


end Counting


namespace Tree

def selected (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun e => e.1 < e.2 ∧ G.Adj e.1 e.2 ∧
    PEqualNP.ReadK.readsAtMost C n [e.1.val,e.2.val] 1 = true)

lemma assembled (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (h4 : PEqualNP.TopForm.NoFourCycle G) (h : PEqualNP.TopForm.IsAO2 n C)
    (hs : ∀ a : Fin n, circuitFun n C (fun k => decide (k=a)) = false)
    (hf : ∀ a b : Fin n, a≠b → ¬G.Adj a b →
      circuitFun n C (fun k => decide (k=a ∨ k=b)) = false) :
    ∃ T : Finset (Fin n), (∀ e∈selected n G C, e.1∈T ∨ e.2∈T) ∧
      (selected n G C).card + T.card ≤ C.size+1 := by
  classical
  by_cases he : (selected n G C).Nonempty
  swap
  · refine ⟨∅,?_,?_⟩
    · intro e he'
      exact False.elim (he ⟨e,he'⟩)
    · rw [Finset.not_nonempty_iff_eq_empty.mp he]
      simp
  obtain ⟨e0,he0⟩ := he
  let T := (J n C).image (centre n C e0.1)
  let Es : Finset (Sym2 (Fin n)) := (J n C).biUnion (fun j =>
    ((singles n C (PEqualNP.TopForm.opnd C j 0)) ×ˢ
      (singles n C (PEqualNP.TopForm.opnd C j 1))).image (fun p => s(p.1,p.2)))
  have hstar := J_star h h4 hs hf
  have hcentre (j : ℕ) (hj : j∈J n C) (a b : Fin n)
      (ha : a∈singles n C (PEqualNP.TopForm.opnd C j 0))
      (hb : b∈singles n C (PEqualNP.TopForm.opnd C j 1)) : a∈T ∨ b∈T := by
    obtain ⟨_,_,_,hL,hR⟩ := mem_J.mp hj
    rcases centre_cross n C e0.1 j hL hR (hstar j hj).2 a b ha hb with hc | hc
    · exact Or.inl (Finset.mem_image.mpr ⟨j,hj,hc⟩)
    · exact Or.inr (Finset.mem_image.mpr ⟨j,hj,hc⟩)
  have hcover : ∀ e∈selected n G C, e.1∈T ∨ e.2∈T := by
    intro e he
    obtain ⟨_,hlt,_,hr⟩ := Finset.mem_filter.mp he
    obtain ⟨j,hj,hj'⟩ := read_pair_join h hs e.1 e.2 (ne_of_lt hlt) hr
    rcases hj' with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact hcentre j hj _ _ ha hb
    · exact (hcentre j hj _ _ ha hb).symm
  have hmap : (selected n G C).image (fun e => s(e.1,e.2)) ⊆ Es := by
    intro e he
    obtain ⟨⟨a,b⟩,hab,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_,hlt,_,hr⟩ := Finset.mem_filter.mp hab
    obtain ⟨j,hj,hj'⟩ := read_pair_join h hs a b (ne_of_lt hlt) hr
    apply Finset.mem_biUnion.mpr
    refine ⟨j,hj,?_⟩
    rcases hj' with ⟨ha,hb⟩ | ⟨hb,ha⟩
    · exact Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩
    · exact Finset.mem_image.mpr ⟨(b,a),Finset.mem_product.mpr ⟨hb,ha⟩,
        Sym2.eq_iff.mpr (Or.inr ⟨rfl,rfl⟩)⟩
  have hinj : Set.InjOn (fun e : Fin n × Fin n => s(e.1,e.2)) (selected n G C) := by
    intro x hx y hy heq
    have hxlt := (Finset.mem_filter.mp hx).2.1
    have hylt := (Finset.mem_filter.mp hy).2.1
    rcases Sym2.eq_iff.mp heq with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · exact Prod.ext h1 h2
    · have h1v := congrArg Fin.val h1
      have h2v := congrArg Fin.val h2
      have hxl : x.1.val < x.2.val := hxlt
      have hyl : y.1.val < y.2.val := hylt
      omega
  have hselected : (selected n G C).card ≤ Es.card := by
    have hc := Finset.card_le_card hmap
    rw [Finset.card_image_iff.mpr hinj] at hc
    exact hc
  have hquad : ∀ a b c d : Fin n, a≠c → b≠d →
      ¬(G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a) := by
    intro a b c d hac hbd hh
    have hc := h4 a c hac
    have hbmem : b∈Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      simp [hh.1,hh.2.1.symm]
    have hdmem : d∈Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj c w) := by
      simp [hh.2.2.2.symm,hh.2.2.1]
    have htwo := Finset.one_lt_card.mpr ⟨b,hbmem,d,hdmem,hbd⟩
    omega
  obtain ⟨⟨Z,hZ,hEs⟩,_⟩ := Counting.assemble2 n G hquad (gateAt C)
    (or_length h) (total_back h) (singles n C) (singles_input_card n C)
    (total_or h) (total_nonor h) (D n C)
    (by
      intro k hk
      rw [singles_empty_path h hs (mem_D.mp hk).2.2]
      simp)
    (J n C) (PEqualNP.TopForm.opnd C) hstar Es (by
      intro e he
      obtain ⟨j,hj,he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨⟨a,b⟩,hp,rfl⟩ := Finset.mem_image.mp he
      exact ⟨j,hj,a,(Finset.mem_product.mp hp).1,b,(Finset.mem_product.mp hp).2,rfl⟩)
  have hzreal : ∀ z∈Z, z<C.size := by
    intro z hz
    obtain ⟨_,_,_,j,hj,b,hnrho,hpath,_,_⟩ := hZ z hz
    have hjlt := (mem_J.mp hj).1
    have hle := raw_path_le h hpath
    have hearlier := earlier h ⟨j,hjlt⟩ b
    rw [← opnd_row C ⟨j,hjlt⟩ b] at hearlier
    change PEqualNP.TopForm.opnd C j b < n+j at hearlier
    omega
  have hdj : Disjoint (J n C ∪ D n C) Z := by
    apply Finset.disjoint_left.mpr
    intro j hj hz
    obtain ⟨hnotD,hor,_⟩ := hZ j hz
    rcases Finset.mem_union.mp hj with hj | hj
    · have hand := (mem_J.mp hj).2.1
      cases hand.symm.trans hor
    · exact hnotD hj
  have hall : (J n C ∪ D n C) ∪ Z ⊆ Finset.range C.size := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · rcases Finset.mem_union.mp hj with hj | hj
      · exact Finset.mem_range.mpr (mem_J.mp hj).1
      · exact Finset.mem_range.mpr (mem_D.mp hj).1
    · exact Finset.mem_range.mpr (hzreal j hj)
  have hbudget := Finset.card_le_card hall
  rw [Finset.card_union_of_disjoint hdj,
    Finset.card_union_of_disjoint (J_disjoint_D n C),Finset.card_range] at hbudget
  have hT : T.card ≤ (J n C).card := Finset.card_image_le
  have hJD := J_card_le_D h
  refine ⟨T,hcover,?_⟩
  omega

end Tree

end PEqualNP.Outside.L_meta_2235

theorem PEqualNP.Outside.L_meta_2235 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → (∀ a1 : Fin n, PEqualNP.MetaComplexity.circuitFun n C (fun k1 => decide (k1 = a1)) = false) → (∀ a2 b2 : Fin n, a2 ≠ b2 → ¬ G.Adj a2 b2 → PEqualNP.MetaComplexity.circuitFun n C (fun k2 => decide (k2 = a2 ∨ k2 = b2)) = false) → ∃ T : Finset (Fin n), (∀ e ∈ (Finset.univ.filter (fun e1 : Fin n × Fin n => e1.1 < e1.2 ∧ G.Adj e1.1 e1.2 ∧ PEqualNP.ReadK.readsAtMost C n [e1.1.val, e1.2.val] 1 = true)), e.1 ∈ T ∨ e.2 ∈ T) ∧ (Finset.univ.filter (fun e2 : Fin n × Fin n => e2.1 < e2.2 ∧ G.Adj e2.1 e2.2 ∧ PEqualNP.ReadK.readsAtMost C n [e2.1.val, e2.2.val] 1 = true)).card + T.card ≤ C.size + 1 := by
  intro n G _ C h4 h hs hf
  simpa [PEqualNP.Outside.L_meta_2235.Tree.selected] using
    PEqualNP.Outside.L_meta_2235.Tree.assembled n G C h4 h hs hf
