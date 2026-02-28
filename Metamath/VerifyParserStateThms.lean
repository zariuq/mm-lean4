import Metamath.Verify
import Metamath.VerifyDBThms

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace Metamath
namespace Verify
namespace ParserState

-- Helper lemmas for Id monad proofs
@[simp] theorem pure_db_config (s : ParserState) : (pure s : Id ParserState).db.config = s.db.config := rfl
@[simp] theorem Id_run_db_config (m : Id ParserState) : (Id.run m).db.config = m.db.config := rfl

@[simp] theorem withDB_db_config (f : DB → DB) (s : ParserState) :
    (s.withDB f).db.config = (f s.db).config := rfl

@[simp] theorem mkError_db_config (s : ParserState) (pos : Pos) (msg : String) :
    (s.mkError pos msg).db.config = s.db.config := by
  unfold ParserState.mkError ParserState.withDB DB.mkError DB.mkErrorWithEvidence
  rfl

@[simp] theorem mkErrorWithEvidence_db_config (s : ParserState) (pos : Pos) (msg : String)
    (ev : ErrorEvidence) :
    (s.mkErrorWithEvidence pos msg ev).db.config = s.db.config := by
  unfold ParserState.mkErrorWithEvidence ParserState.withDB DB.mkErrorWithEvidence
  rfl

@[simp] theorem mkErrorAt_db_config (s : ParserState) (pos : Pos) (l msg : String) :
    (s.mkErrorAt pos l msg).db.config = s.db.config := by
  simp [ParserState.mkErrorAt]

@[simp] theorem mkErrorFromEvidence_db_config (s : ParserState) (pos : Pos) (ev : ErrorEvidence) :
    (s.mkErrorFromEvidence pos ev).db.config = s.db.config := by
  simp [ParserState.mkErrorFromEvidence, ParserState.withDB]

@[simp] theorem withAt_tokp (l : String) (f : Unit → ParserState) :
    (ParserState.withAt l f).tokp = (f ()).tokp := by
  unfold ParserState.withAt
  generalize hs : f () = s0
  cases h_err : s0.db.error? with
  | none =>
      simp [h_err]
  | some intr =>
      cases intr with
      | mk e idx =>
          cases e <;> simp [h_err, ParserState.withDB]

@[simp] theorem withAt_parseErrorCode? (l : String) (f : Unit → ParserState) :
    (ParserState.withAt l f).db.parseErrorCode? = (f ()).db.parseErrorCode? := by
  unfold ParserState.withAt
  generalize hs : f () = s0
  cases h_err : s0.db.error? with
  | none =>
      simp [h_err, DB.parseErrorCode?]
  | some intr =>
      cases intr with
      | mk e idx =>
          cases e <;> simp [h_err, ParserState.withDB, DB.parseErrorCode?]

@[simp] theorem withAt_db_config (l : String) (f : Unit → ParserState) :
    (ParserState.withAt l f).db.config = (f ()).db.config := by
  unfold ParserState.withAt
  generalize hs : f () = s0
  cases h_err : s0.db.error? with
  | none =>
      simp [h_err]
  | some intr =>
      cases intr with
      | mk e idx =>
          cases e <;> simp [h_err, ParserState.withDB]

@[simp] theorem resumeAxiom_db_config (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) :
    (s.resumeAxiom pos l fmla fr).db.config = s.db.config := by
  simp [ParserState.resumeAxiom, ParserState.withDB, DB.insert_config]

@[simp] theorem label_db_config (s : ParserState) (pos : Pos) (tk : ByteSlice) :
    (s.label pos tk).db.config = s.db.config := by
  unfold ParserState.label
  split <;> split <;> simp [ParserState.mkErrorFromEvidence_db_config]

@[simp] theorem withMath_db_config (s : ParserState) (pos : Pos) (tk : ByteSlice)
    (f : ParserState → String → ParserState)
    (hf : ∀ tk', (f s tk').db.config = s.db.config) :
    (s.withMath pos tk f).db.config = s.db.config := by
  unfold ParserState.withMath
  split
  · split
    · simp [ParserState.mkErrorFromEvidence_db_config]
    · exact hf _

@[simp] theorem djvars_loop_aux_db_config (arr : Array String) (s : ParserState)
    (pos : Pos) (tk : String) (i : Nat) :
    (djvars_loop_aux arr s pos tk i).db.config = s.db.config := by
  refine Nat.rec (motive := fun m => ∀ i (s : ParserState), arr.size - i = m →
      (djvars_loop_aux arr s pos tk i).db.config = s.db.config) ?base ?step (arr.size - i) i s rfl
  · intro i s hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simpa [hs] using hpos
    simp [djvars_loop_aux, hi]
  · intro m ih i s hs
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      ·
        have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        have : False := by
          have hs' := hs
          simpa [hz] using hs'
        exact False.elim this
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    unfold djvars_loop_aux
    simp only [hi, ↓reduceDIte]
    split
    · simp [ParserState.mkErrorFromEvidence_db_config]
    ·
      have h_cfg : (s.withDB
          (fun db =>
            db.withDJ
              fun dj => dj.push (if arr[i] < tk then (arr[i], tk) else (tk, arr[i])))).db.config
          = s.db.config := by
        simp [ParserState.withDB, DB.withDJ_config]
      simpa [h_cfg] using ih (i + 1) _ hs'

@[simp] theorem djvars_loop_db_config (arr : Array String) (s : ParserState)
    (pos : Pos) (tk : String) :
    (djvars_loop arr s pos tk).db.config = s.db.config := by
  unfold djvars_loop
  cases h_gate : s.db.djvarsScopeViolation? tk with
  | none =>
      simp [h_gate, djvars_loop_aux_db_config]
  | some err =>
      simp [h_gate, ParserState.mkErrorFromEvidence_db_config]

@[simp] theorem sym_db_config (s : ParserState) (pos : Pos) (tk : ByteSlice) (f : String → Object) :
    (s.sym pos tk f).db.config = s.db.config := by
  unfold ParserState.sym ParserState.withMath
  by_cases h_end : tk.eqArray "$.".toAscii
  · simp [h_end]
  · simp only [h_end, Bool.false_eq_true, ↓reduceIte]
    by_cases h_ok : (toMath tk).fst = false
    · simp [h_ok, ParserState.mkErrorFromEvidence_db_config]
    · simp [h_ok, ParserState.withDB, DB.insert_config]

@[simp] theorem resumeThm_db_config (s : ParserState)
    (pos : Pos) (l : String) (fmla : Formula) (fr : Frame) :
    (s.resumeThm pos l fmla fr).db.config = s.db.config := by
  simp [ParserState.resumeThm]

@[simp] theorem feedTokens_db_config (s : ParserState) (arr : Array Sym) (p : TokensParser) :
    (s.feedTokens arr p).db.config = s.db.config := by
  cases p with
  | mk k pos l =>
      unfold ParserState.feedTokens
      simp only [ParserState.withAt_db_config, ParserState.Id_run_db_config]
      repeat
        (first
          | split
          | simp
              [ParserState.mkErrorFromEvidence_db_config, ParserState.withDB, DB.insertHyp_config,
                DB.insertAxiom_config, ParserState.resumeThm_db_config, ParserState.pure_db_config]
          | rfl)

@[simp] theorem feedProof_db_config (s : ParserState) (tk : ByteSlice) (pr : ProofState) :
    (s.feedProof tk pr).db.config = s.db.config := by
  unfold ParserState.feedProof
  simp only [ParserState.withAt_db_config]
  split <;> simp [ParserState.mkErrorFromEvidence_db_config]

@[simp] theorem finishProof_db_config (s : ParserState) (pr : ProofState) :
    (s.finishProof pr).db.config = s.db.config := by
  cases pr with
  | mk pos l fmla fr heap stack ptp =>
      unfold ParserState.finishProof
      simp only [ParserState.withAt_db_config, Id.run]
      cases ptp with
      | start => simp [ParserState.mkErrorFromEvidence_db_config]
      | preload => simp [ParserState.mkErrorFromEvidence_db_config]
      | normal =>
          simp only [Pure.pure, Bind.bind]
          split
          · split <;> simp [ParserState.mkErrorFromEvidence_db_config, ParserState.withDB, DB.insert_config]
          · simp [ParserState.mkErrorFromEvidence_db_config]
      | compressed chr =>
          simp only [Pure.pure, Bind.bind]
          split
          ·
            split
            · split <;> simp [ParserState.mkErrorFromEvidence_db_config, ParserState.withDB, DB.insert_config]
            · simp [ParserState.mkErrorFromEvidence_db_config]
          ·
            split
            · split <;> simp [ParserState.mkErrorFromEvidence_db_config, ParserState.withDB, DB.insert_config]
            · simp [ParserState.mkErrorFromEvidence_db_config]
          · simp [ParserState.mkErrorFromEvidence_db_config]

@[simp] theorem feedToken_db_config (s : ParserState) (pos : Nat) (tk : ByteSlice) :
    (s.feedToken pos tk).db.config = s.db.config := by
  unfold ParserState.feedToken
  cases s.tokp with
  | comment p =>
      simp only []
      split
      · rfl
      · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
  | start =>
      simp only []
      split
      · rfl
      · split
        ·
          split <;> simp [ParserState.mkErrorFromEvidence_db_config]
        ·
          split
          ·
            split <;>
              simp [ParserState.withDB, DB.pushScope_config, DB.popScope_config,
                ParserState.label_db_config]
          · simp [ParserState.label_db_config]
  | const =>
      simp only []
      split
      · rfl
      · split
        · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
        · simp [ParserState.sym_db_config]
  | var =>
      simp only []
      split
      · rfl
      · split
        · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
        · simp [ParserState.sym_db_config]
  | djvars arr =>
      simp only []
      split
      · rfl
      · split
        · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
        ·
          split
          · rfl
          · simp [ParserState.djvars_loop_db_config]
  | math arr' p =>
      simp only []
      split
      · rfl
      · split
        · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
        ·
          split
          · simp [ParserState.feedTokens_db_config]
          ·
            apply ParserState.withMath_db_config
            intro tk1
            simp only [Id.run, Pure.pure, Bind.bind]
            cases h_find : s.db.find? tk1 with
            | none =>
                cases h_gate : s.db.mathSymbolViolation? tk1 <;>
                  simp [h_find, h_gate, ParserState.mkErrorFromEvidence_db_config]
            | some obj =>
                cases obj with
                | const _ => simp [h_find]
                | var _ => simp [h_find]
                | hyp _ _ _ =>
                    cases h_gate : s.db.mathSymbolViolation? tk1 <;>
                      simp [h_find, h_gate, ParserState.mkErrorFromEvidence_db_config]
                | assert _ _ _ =>
                    cases h_gate : s.db.mathSymbolViolation? tk1 <;>
                      simp [h_find, h_gate, ParserState.mkErrorFromEvidence_db_config]
  | label pos' lab =>
      simp only []
      split
      · rfl
      · split
        · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
        ·
          split
          · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
          · simp [ParserState.mkErrorFromEvidence_db_config]
  | includePath includePos =>
      simp only []
      split
      · rfl
      · split
        · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
        ·
          split
          · simp [ParserState.mkErrorFromEvidence_db_config]
          ·
            unfold ParserState.normalizeIncludePath
            split
            · simp [ParserState.mkErrorFromEvidence_db_config]
            ·
              split
              · rfl
              ·
                by_cases h_req : (ParserState.includePathFromToken tk).snd = true
                · simp [h_req, ParserState.requestInclude]
                · simp [h_req]
  | includeClose includePos includePath =>
      simp only []
      split
      · rfl
      · split
        · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
        ·
          split
          · simp [ParserState.requestInclude]
          · simp [ParserState.mkErrorFromEvidence_db_config]
  | proof pr =>
      simp only []
      split
      · rfl
      · split
        · split <;> simp [ParserState.mkErrorFromEvidence_db_config]
        · split <;> simp [ParserState.finishProof_db_config, ParserState.feedProof_db_config]

@[simp] theorem updateLine_db (s : ParserState) (i : Nat) (c : UInt8) :
    (s.updateLine i c).db = s.db := by
  unfold ParserState.updateLine
  split <;> rfl

@[simp] theorem updateLine_db_config (s : ParserState) (i : Nat) (c : UInt8) :
    (s.updateLine i c).db.config = s.db.config := by
  simp [updateLine_db]

@[simp] theorem feed_db_config (base : Nat) (arr : ByteArray) (i : Nat) (rs : FeedState) (s : ParserState) :
    (s.feed base arr i rs).db.config = s.db.config := by
  refine Nat.rec (motive := fun m => ∀ i rs (s : ParserState), arr.size - i = m →
      (s.feed base arr i rs).db.config = s.db.config) ?base ?step (arr.size - i) i rs s rfl
  · intro i rs s hs
    have hi : ¬ i < arr.size := by
      intro hi
      have hpos : arr.size - i > 0 := Nat.sub_pos_of_lt hi
      simpa [hs] using hpos
    unfold ParserState.feed
    simp only [hi, ↓reduceDIte]
  · intro m ih i rs s hs
    have hi : i < arr.size := by
      by_cases hi' : i < arr.size
      · exact hi'
      ·
        have hz : arr.size - i = 0 := Nat.sub_eq_zero_of_le (Nat.le_of_not_gt hi')
        have : False := by
          have hs' := hs
          simpa [hz] using hs'
        exact False.elim this
    have hs' : arr.size - (i + 1) = m := by
      simp only [Nat.add_one, Nat.sub_succ, hs, Nat.pred_succ]
    let c := arr[i]
    by_cases h_ws : isWhitespace c
    · cases rs with
      | ws =>
          have hrec := ih (i + 1) FeedState.ws (s.updateLine (base + i) c) hs'
          simp only [ParserState.updateLine_db_config] at hrec
          unfold ParserState.feed
          have h_ws' : isWhitespace arr[i] = true := h_ws
          simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte]
          exact hrec
      | token ot =>
          have hs0 :
              (match ot with
              | .this off => (s.feedToken (base + off) (ByteSlice.mk arr off (i - off))).db.config
              | .old base' off arr' =>
                  (s.feedToken (base + off)
                    (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))).db.config)
                = s.db.config := by
            cases ot <;> simp [ParserState.feedToken_db_config]
          cases ot with
          | this off =>
              let s0 := s.feedToken (base + off) (ByteSlice.mk arr off (i - off))
              let s1 : ParserState := s0.updateLine (base + i) arr[i]
              have hs1 : s1.db.config = s.db.config := by
                simp only [s1, ParserState.updateLine_db_config, s0, ParserState.feedToken_db_config]
              have h_ws' : isWhitespace arr[i] = true := h_ws
              cases h_err : s1.db.error? with
              | some intr =>
                  unfold ParserState.feed
                  simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte, s0, s1, h_err, hs1]
              | none =>
                  have hrec := ih (i + 1) FeedState.ws s1 hs'
                  unfold ParserState.feed
                  simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte, s0, s1, h_err]
                  exact hrec.trans hs1
          | old base' off arr' =>
              let s0 := s.feedToken (base' + off)
                (ByteSlice.mk (arr.copySlice 0 arr' arr'.size i false) off (arr'.size - off + i))
              let s1 : ParserState := s0.updateLine (base + i) arr[i]
              have hs1 : s1.db.config = s.db.config := by
                simp only [s1, ParserState.updateLine_db_config, s0, ParserState.feedToken_db_config]
              have h_ws' : isWhitespace arr[i] = true := h_ws
              cases h_err : s1.db.error? with
              | some intr =>
                  unfold ParserState.feed
                  simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte, s0, s1, h_err, hs1]
              | none =>
                  have hrec := ih (i + 1) FeedState.ws s1 hs'
                  unfold ParserState.feed
                  simp only [hi, h_ws', ↓reduceDIte, ↓reduceIte, s0, s1, h_err]
                  exact hrec.trans hs1
    · have h_ws' : ¬ isWhitespace arr[i] = true := h_ws
      cases rs with
      | ws =>
          have hrec := ih (i + 1) (FeedState.token (OldToken.this i)) s hs'
          unfold ParserState.feed
          simp only [hi, h_ws', ↓reduceDIte]
          exact hrec
      | token ot =>
          have hrec := ih (i + 1) (FeedState.token ot) s hs'
          unfold ParserState.feed
          simp only [hi, h_ws', ↓reduceDIte]
          exact hrec

@[simp] theorem feedAll_db_config (s : ParserState) (base : Nat) (arr : ByteArray) :
    (s.feedAll base arr).db.config = s.db.config := by
  cases h : s.charp with
  | ws =>
      simp [ParserState.feedAll, h, ParserState.feed_db_config]
  | token base' tk =>
      simp [ParserState.feedAll, h, ParserState.feed_db_config]

@[simp] theorem done_config (s : ParserState) (base : Nat) :
    (s.done base).config = s.db.config := by
  by_cases h_err0 : s.db.error?.isSome = true
  · unfold ParserState.done
    simp [h_err0, DB.error, Bind.bind, Id.run, Pure.pure]
  · cases h_charp : s.charp with
    | ws =>
        unfold ParserState.done
        simp [h_err0, h_charp, DB.error, Bind.bind, Id.run, Pure.pure]
        cases h_tokp : s.tokp with
        | start =>
            by_cases h_scope : 0 < s.db.scopes.size
            · simp [h_tokp, h_scope, DB.mkErrorFromEvidence_config]
            · simp [h_tokp, h_scope]
        | comment _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | const =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | var =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | djvars _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | math _ p =>
            cases h_k : p.k <;> simp [h_tokp, h_k, DB.mkErrorFromEvidence_config]
        | label _ _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | includePath _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | includeClose _ _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
        | proof _ =>
            simp [h_tokp, DB.mkErrorFromEvidence_config]
    | token pos tk =>
        by_cases h_err1 : (s.feedToken pos tk.toSlice).db.error?.isSome = true
        · unfold ParserState.done
          simp [h_err0, h_charp, h_err1, DB.error, Bind.bind, Id.run, Pure.pure,
            ParserState.feedToken_db_config]
        · unfold ParserState.done
          simp [h_err0, h_charp, h_err1, DB.error, Bind.bind, Id.run, Pure.pure,
            ParserState.feedToken_db_config]
          cases h_tokp : (s.feedToken pos tk.toSlice).tokp with
          | start =>
              by_cases h_scope : 0 < (s.feedToken pos tk.toSlice).db.scopes.size
              · simp [h_tokp, h_scope, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
              · simp [h_tokp, h_scope, ParserState.feedToken_db_config]
          | comment _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | const =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | var =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | djvars _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | math _ p =>
              cases h_k : p.k <;>
                simp [h_tokp, h_k, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | label _ _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | includePath _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | includeClose _ _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]
          | proof _ =>
              simp [h_tokp, DB.mkErrorFromEvidence_config, ParserState.feedToken_db_config]

end ParserState
end Verify
end Metamath
