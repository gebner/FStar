open Prims
exception Un_extractable 
let (uu___is_Un_extractable : Prims.exn -> Prims.bool) =
  fun projectee ->
    match projectee with | Un_extractable -> true | uu___ -> false
let (type_leq :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool)
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Extraction_ML_Util.type_leq
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let (type_leq_c :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool * FStar_Extraction_ML_Syntax.mlexpr
            FStar_Pervasives_Native.option))
  =
  fun g ->
    fun t1 ->
      fun t2 ->
        FStar_Extraction_ML_Util.type_leq_c
          (FStar_Extraction_ML_Util.udelta_unfold g) t1 t2
let (eraseTypeDeep :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t ->
      FStar_Extraction_ML_Util.eraseTypeDeep
        (FStar_Extraction_ML_Util.udelta_unfold g) t
let fail :
  'uuuuu .
    FStar_Compiler_Range_Type.range ->
      (FStar_Errors_Codes.raw_error * Prims.string) -> 'uuuuu
  = fun r -> fun err -> FStar_Errors.raise_error err r
let err_ill_typed_application :
  'uuuuu 'uuuuu1 .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.term ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          (FStar_Syntax_Syntax.term * 'uuuuu) Prims.list ->
            FStar_Extraction_ML_Syntax.mlty -> 'uuuuu1
  =
  fun env ->
    fun t ->
      fun mlhead ->
        fun args ->
          fun ty ->
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.term_to_string t in
                let uu___3 =
                  let uu___4 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env in
                  FStar_Extraction_ML_Code.string_of_mlexpr uu___4 mlhead in
                let uu___4 =
                  let uu___5 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env in
                  FStar_Extraction_ML_Code.string_of_mlty uu___5 ty in
                let uu___5 =
                  let uu___6 =
                    FStar_Compiler_Effect.op_Bar_Greater args
                      (FStar_Compiler_List.map
                         (fun uu___7 ->
                            match uu___7 with
                            | (x, uu___8) ->
                                FStar_Syntax_Print.term_to_string x)) in
                  FStar_Compiler_Effect.op_Bar_Greater uu___6
                    (FStar_String.concat " ") in
                FStar_Compiler_Util.format4
                  "Ill-typed application: source application is %s \n translated prefix to %s at type %s\n remaining args are %s\n"
                  uu___2 uu___3 uu___4 uu___5 in
              (FStar_Errors_Codes.Fatal_IllTyped, uu___1) in
            fail t.FStar_Syntax_Syntax.pos uu___
let err_ill_typed_erasure :
  'uuuuu .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Compiler_Range_Type.range ->
        FStar_Extraction_ML_Syntax.mlty -> 'uuuuu
  =
  fun env ->
    fun pos ->
      fun ty ->
        let uu___ =
          let uu___1 =
            let uu___2 =
              let uu___3 =
                FStar_Extraction_ML_UEnv.current_module_of_uenv env in
              FStar_Extraction_ML_Code.string_of_mlty uu___3 ty in
            FStar_Compiler_Util.format1
              "Erased value found where a value of type %s was expected"
              uu___2 in
          (FStar_Errors_Codes.Fatal_IllTyped, uu___1) in
        fail pos uu___
let err_value_restriction :
  'uuuuu . FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax -> 'uuuuu =
  fun t ->
    let uu___ =
      let uu___1 =
        let uu___2 = FStar_Syntax_Print.tag_of_term t in
        let uu___3 = FStar_Syntax_Print.term_to_string t in
        FStar_Compiler_Util.format2
          "Refusing to generalize because of the value restriction: (%s) %s"
          uu___2 uu___3 in
      (FStar_Errors_Codes.Fatal_ValueRestriction, uu___1) in
    fail t.FStar_Syntax_Syntax.pos uu___
let (err_unexpected_eff :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.e_tag ->
          FStar_Extraction_ML_Syntax.e_tag -> unit)
  =
  fun env ->
    fun t ->
      fun ty ->
        fun f0 ->
          fun f1 ->
            let uu___ =
              let uu___1 =
                let uu___2 = FStar_Syntax_Print.term_to_string t in
                let uu___3 =
                  let uu___4 =
                    FStar_Extraction_ML_UEnv.current_module_of_uenv env in
                  FStar_Extraction_ML_Code.string_of_mlty uu___4 ty in
                let uu___4 = FStar_Extraction_ML_Util.eff_to_string f0 in
                let uu___5 = FStar_Extraction_ML_Util.eff_to_string f1 in
                FStar_Compiler_Util.format4
                  "for expression %s of type %s, Expected effect %s; got effect %s"
                  uu___2 uu___3 uu___4 uu___5 in
              (FStar_Errors_Codes.Warning_ExtractionUnexpectedEffect, uu___1) in
            FStar_Errors.log_issue t.FStar_Syntax_Syntax.pos uu___
let err_cannot_extract_effect :
  'uuuuu .
    FStar_Ident.lident ->
      FStar_Compiler_Range_Type.range ->
        Prims.string -> Prims.string -> 'uuuuu
  =
  fun l ->
    fun r ->
      fun reason ->
        fun ctxt ->
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 = FStar_Ident.string_of_lid l in
                  FStar_Compiler_Util.format3
                    "Cannot extract effect %s because %s (when extracting %s)"
                    uu___4 reason ctxt in
                FStar_Compiler_Effect.op_Less_Bar FStar_Errors_Msg.text
                  uu___3 in
              [uu___2] in
            (FStar_Errors_Codes.Fatal_UnexpectedEffect, uu___1) in
          FStar_Errors.raise_error_doc uu___ r
let (effect_as_etag :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident -> FStar_Extraction_ML_Syntax.e_tag)
  =
  let cache = FStar_Compiler_Util.smap_create (Prims.of_int (20)) in
  let rec delta_norm_eff g l =
    let uu___ =
      let uu___1 = FStar_Ident.string_of_lid l in
      FStar_Compiler_Util.smap_try_find cache uu___1 in
    match uu___ with
    | FStar_Pervasives_Native.Some l1 -> l1
    | FStar_Pervasives_Native.None ->
        let res =
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
            FStar_TypeChecker_Env.lookup_effect_abbrev uu___2
              [FStar_Syntax_Syntax.U_zero] l in
          match uu___1 with
          | FStar_Pervasives_Native.None -> l
          | FStar_Pervasives_Native.Some (uu___2, c) ->
              delta_norm_eff g (FStar_Syntax_Util.comp_effect_name c) in
        ((let uu___2 = FStar_Ident.string_of_lid l in
          FStar_Compiler_Util.smap_add cache uu___2 res);
         res) in
  fun g ->
    fun l ->
      let l1 = delta_norm_eff g l in
      let uu___ =
        FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_PURE_lid in
      if uu___
      then FStar_Extraction_ML_Syntax.E_PURE
      else
        (let uu___2 =
           let uu___3 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
           FStar_TypeChecker_Env.is_erasable_effect uu___3 l1 in
         if uu___2
         then FStar_Extraction_ML_Syntax.E_ERASABLE
         else
           (let ed_opt =
              let uu___4 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
              FStar_TypeChecker_Env.effect_decl_opt uu___4 l1 in
            match ed_opt with
            | FStar_Pervasives_Native.Some (ed, qualifiers) ->
                let uu___4 =
                  let uu___5 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                  FStar_TypeChecker_Env.is_reifiable_effect uu___5
                    ed.FStar_Syntax_Syntax.mname in
                if uu___4
                then FStar_Extraction_ML_Syntax.E_PURE
                else FStar_Extraction_ML_Syntax.E_IMPURE
            | FStar_Pervasives_Native.None ->
                FStar_Extraction_ML_Syntax.E_IMPURE))
let rec (is_arity_aux :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun tcenv ->
    fun t ->
      let t1 = FStar_Syntax_Util.unmeta t in
      let uu___ =
        let uu___1 = FStar_Syntax_Subst.compress t1 in
        uu___1.FStar_Syntax_Syntax.n in
      match uu___ with
      | FStar_Syntax_Syntax.Tm_unknown -> failwith "Impossible: is_arity"
      | FStar_Syntax_Syntax.Tm_delayed uu___1 ->
          failwith "Impossible: is_arity"
      | FStar_Syntax_Syntax.Tm_ascribed uu___1 ->
          failwith "Impossible: is_arity"
      | FStar_Syntax_Syntax.Tm_meta uu___1 -> failwith "Impossible: is_arity"
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu___1 = FStar_Syntax_Util.unfold_lazy i in
          is_arity_aux tcenv uu___1
      | FStar_Syntax_Syntax.Tm_uvar uu___1 -> false
      | FStar_Syntax_Syntax.Tm_constant uu___1 -> false
      | FStar_Syntax_Syntax.Tm_name uu___1 -> false
      | FStar_Syntax_Syntax.Tm_quoted uu___1 -> false
      | FStar_Syntax_Syntax.Tm_bvar uu___1 -> false
      | FStar_Syntax_Syntax.Tm_type uu___1 -> true
      | FStar_Syntax_Syntax.Tm_arrow
          { FStar_Syntax_Syntax.bs1 = uu___1; FStar_Syntax_Syntax.comp = c;_}
          -> is_arity_aux tcenv (FStar_Syntax_Util.comp_result c)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let topt =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Unfold
                 FStar_Syntax_Syntax.delta_constant] tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match topt with
           | FStar_Pervasives_Native.None -> false
           | FStar_Pervasives_Native.Some (uu___1, t2) ->
               is_arity_aux tcenv t2)
      | FStar_Syntax_Syntax.Tm_app uu___1 ->
          let uu___2 = FStar_Syntax_Util.head_and_args t1 in
          (match uu___2 with | (head, uu___3) -> is_arity_aux tcenv head)
      | FStar_Syntax_Syntax.Tm_uinst (head, uu___1) ->
          is_arity_aux tcenv head
      | FStar_Syntax_Syntax.Tm_refine
          { FStar_Syntax_Syntax.b = x; FStar_Syntax_Syntax.phi = uu___1;_} ->
          is_arity_aux tcenv x.FStar_Syntax_Syntax.sort
      | FStar_Syntax_Syntax.Tm_abs
          { FStar_Syntax_Syntax.bs = uu___1; FStar_Syntax_Syntax.body = body;
            FStar_Syntax_Syntax.rc_opt = uu___2;_}
          -> is_arity_aux tcenv body
      | FStar_Syntax_Syntax.Tm_let
          { FStar_Syntax_Syntax.lbs = uu___1;
            FStar_Syntax_Syntax.body1 = body;_}
          -> is_arity_aux tcenv body
      | FStar_Syntax_Syntax.Tm_match
          { FStar_Syntax_Syntax.scrutinee = uu___1;
            FStar_Syntax_Syntax.ret_opt = uu___2;
            FStar_Syntax_Syntax.brs = branches;
            FStar_Syntax_Syntax.rc_opt1 = uu___3;_}
          ->
          (match branches with
           | (uu___4, uu___5, e)::uu___6 -> is_arity_aux tcenv e
           | uu___4 -> false)
let (is_arity :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let uu___ = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
      is_arity_aux uu___ t
let (push_tcenv_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders -> FStar_Extraction_ML_UEnv.uenv)
  =
  fun u ->
    fun bs ->
      let tcenv = FStar_Extraction_ML_UEnv.tcenv_of_uenv u in
      let tcenv1 = FStar_TypeChecker_Env.push_binders tcenv bs in
      FStar_Extraction_ML_UEnv.set_tcenv u tcenv1
let rec (is_type_aux :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_delayed uu___ ->
          let uu___1 =
            let uu___2 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Compiler_Util.format1 "Impossible: %s" uu___2 in
          failwith uu___1
      | FStar_Syntax_Syntax.Tm_unknown ->
          let uu___ =
            let uu___1 = FStar_Syntax_Print.tag_of_term t1 in
            FStar_Compiler_Util.format1 "Impossible: %s" uu___1 in
          failwith uu___
      | FStar_Syntax_Syntax.Tm_lazy i ->
          let uu___ = FStar_Syntax_Util.unfold_lazy i in
          is_type_aux env uu___
      | FStar_Syntax_Syntax.Tm_constant uu___ -> false
      | FStar_Syntax_Syntax.Tm_type uu___ -> true
      | FStar_Syntax_Syntax.Tm_refine uu___ -> true
      | FStar_Syntax_Syntax.Tm_arrow uu___ -> true
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu___ = FStar_Parser_Const.failwith_lid () in
          FStar_Syntax_Syntax.fv_eq_lid fv uu___ -> false
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          FStar_Extraction_ML_UEnv.is_type_name env fv
      | FStar_Syntax_Syntax.Tm_uvar (u, s) ->
          let t2 = FStar_Syntax_Util.ctx_uvar_typ u in
          let uu___ = FStar_Syntax_Subst.subst' s t2 in is_arity env uu___
      | FStar_Syntax_Syntax.Tm_bvar
          { FStar_Syntax_Syntax.ppname = uu___;
            FStar_Syntax_Syntax.index = uu___1;
            FStar_Syntax_Syntax.sort = t2;_}
          -> is_arity env t2
      | FStar_Syntax_Syntax.Tm_name x ->
          let g = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
          let uu___ = FStar_TypeChecker_Env.try_lookup_bv g x in
          (match uu___ with
           | FStar_Pervasives_Native.Some (t2, uu___1) -> is_arity env t2
           | uu___1 ->
               let uu___2 =
                 let uu___3 = FStar_Syntax_Print.tag_of_term t1 in
                 FStar_Compiler_Util.format1
                   "Extraction: variable not found: %s" uu___3 in
               failwith uu___2)
      | FStar_Syntax_Syntax.Tm_ascribed
          { FStar_Syntax_Syntax.tm = t2; FStar_Syntax_Syntax.asc = uu___;
            FStar_Syntax_Syntax.eff_opt = uu___1;_}
          -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_uinst (t2, uu___) -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_abs
          { FStar_Syntax_Syntax.bs = bs; FStar_Syntax_Syntax.body = body;
            FStar_Syntax_Syntax.rc_opt = uu___;_}
          ->
          let uu___1 = FStar_Syntax_Subst.open_term bs body in
          (match uu___1 with
           | (bs1, body1) ->
               let env1 = push_tcenv_binders env bs1 in
               is_type_aux env1 body1)
      | FStar_Syntax_Syntax.Tm_let
          { FStar_Syntax_Syntax.lbs = (false, lb::[]);
            FStar_Syntax_Syntax.body1 = body;_}
          ->
          let x = FStar_Compiler_Util.left lb.FStar_Syntax_Syntax.lbname in
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Syntax_Syntax.mk_binder x in [uu___2] in
            FStar_Syntax_Subst.open_term uu___1 body in
          (match uu___ with
           | (bs, body1) ->
               let env1 = push_tcenv_binders env bs in is_type_aux env1 body1)
      | FStar_Syntax_Syntax.Tm_let
          { FStar_Syntax_Syntax.lbs = (uu___, lbs);
            FStar_Syntax_Syntax.body1 = body;_}
          ->
          let uu___1 = FStar_Syntax_Subst.open_let_rec lbs body in
          (match uu___1 with
           | (lbs1, body1) ->
               let env1 =
                 let uu___2 =
                   FStar_Compiler_List.map
                     (fun lb ->
                        let uu___3 =
                          FStar_Compiler_Util.left
                            lb.FStar_Syntax_Syntax.lbname in
                        FStar_Syntax_Syntax.mk_binder uu___3) lbs1 in
                 push_tcenv_binders env uu___2 in
               is_type_aux env1 body1)
      | FStar_Syntax_Syntax.Tm_match
          { FStar_Syntax_Syntax.scrutinee = uu___;
            FStar_Syntax_Syntax.ret_opt = uu___1;
            FStar_Syntax_Syntax.brs = branches;
            FStar_Syntax_Syntax.rc_opt1 = uu___2;_}
          ->
          (match branches with
           | b::uu___3 ->
               let uu___4 = FStar_Syntax_Subst.open_branch b in
               (match uu___4 with
                | (pat, uu___5, e) ->
                    let uu___6 =
                      let uu___7 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
                      FStar_TypeChecker_PatternUtils.raw_pat_as_exp uu___7
                        pat in
                    (match uu___6 with
                     | FStar_Pervasives_Native.None -> false
                     | FStar_Pervasives_Native.Some (uu___7, bvs) ->
                         let binders =
                           FStar_Compiler_List.map
                             (fun bv -> FStar_Syntax_Syntax.mk_binder bv) bvs in
                         let env1 = push_tcenv_binders env binders in
                         is_type_aux env1 e))
           | uu___3 -> false)
      | FStar_Syntax_Syntax.Tm_quoted uu___ -> false
      | FStar_Syntax_Syntax.Tm_meta
          { FStar_Syntax_Syntax.tm2 = t2; FStar_Syntax_Syntax.meta = uu___;_}
          -> is_type_aux env t2
      | FStar_Syntax_Syntax.Tm_app
          { FStar_Syntax_Syntax.hd = head;
            FStar_Syntax_Syntax.args = uu___;_}
          -> is_type_aux env head
let (is_type :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env ->
    fun t ->
      FStar_Extraction_ML_UEnv.debug env
        (fun uu___1 ->
           let uu___2 = FStar_Syntax_Print.tag_of_term t in
           let uu___3 = FStar_Syntax_Print.term_to_string t in
           FStar_Compiler_Util.print2 "checking is_type (%s) %s\n" uu___2
             uu___3);
      (let b = is_type_aux env t in
       FStar_Extraction_ML_UEnv.debug env
         (fun uu___2 ->
            if b
            then
              let uu___3 = FStar_Syntax_Print.term_to_string t in
              let uu___4 = FStar_Syntax_Print.tag_of_term t in
              FStar_Compiler_Util.print2 "yes, is_type %s (%s)\n" uu___3
                uu___4
            else
              (let uu___4 = FStar_Syntax_Print.term_to_string t in
               let uu___5 = FStar_Syntax_Print.tag_of_term t in
               FStar_Compiler_Util.print2 "not a type %s (%s)\n" uu___4
                 uu___5));
       b)
let (is_steel_with_invariant_g : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst head in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            _a::_fp::_fp'::_o::_p::_i::_body::[]) ->
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.steel_with_invariant_g_lid)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.steel_st_with_invariant_g_lid)
         | uu___2 -> false)
let (is_steel_with_invariant :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term FStar_Pervasives_Native.option)
  =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst head in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv,
            _a::_fp::_fp'::_o::_obs::_p::_i::body::[]) when
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.steel_with_invariant_lid)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.steel_st_with_invariant_lid)
             ->
             FStar_Pervasives_Native.Some (FStar_Pervasives_Native.fst body)
         | uu___2 -> FStar_Pervasives_Native.None)
let (is_steel_new_invariant : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStar_Syntax_Util.head_and_args t in
    match uu___ with
    | (head, args) ->
        let uu___1 =
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst head in
            uu___3.FStar_Syntax_Syntax.n in
          (uu___2, args) in
        (match uu___1 with
         | (FStar_Syntax_Syntax.Tm_fvar fv, _o::_p::[]) ->
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.steel_new_invariant_lid)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.steel_st_new_invariant_lid)
         | uu___2 -> false)
let (is_type_binder :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.binder -> Prims.bool)
  =
  fun env ->
    fun x ->
      is_arity env (x.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
let (is_constructor : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu___1;
          FStar_Syntax_Syntax.fv_delta = uu___2;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Data_ctor);_}
        -> true
    | FStar_Syntax_Syntax.Tm_fvar
        { FStar_Syntax_Syntax.fv_name = uu___1;
          FStar_Syntax_Syntax.fv_delta = uu___2;
          FStar_Syntax_Syntax.fv_qual = FStar_Pervasives_Native.Some
            (FStar_Syntax_Syntax.Record_ctor uu___3);_}
        -> true
    | uu___1 -> false
let rec (is_fstar_value : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ =
      let uu___1 = FStar_Syntax_Subst.compress t in
      uu___1.FStar_Syntax_Syntax.n in
    match uu___ with
    | FStar_Syntax_Syntax.Tm_constant uu___1 -> true
    | FStar_Syntax_Syntax.Tm_bvar uu___1 -> true
    | FStar_Syntax_Syntax.Tm_fvar uu___1 -> true
    | FStar_Syntax_Syntax.Tm_abs uu___1 -> true
    | FStar_Syntax_Syntax.Tm_app
        { FStar_Syntax_Syntax.hd = head; FStar_Syntax_Syntax.args = args;_}
        ->
        let uu___1 = is_constructor head in
        if uu___1
        then
          FStar_Compiler_Effect.op_Bar_Greater args
            (FStar_Compiler_List.for_all
               (fun uu___2 ->
                  match uu___2 with | (te, uu___3) -> is_fstar_value te))
        else false
    | FStar_Syntax_Syntax.Tm_meta
        { FStar_Syntax_Syntax.tm2 = t1; FStar_Syntax_Syntax.meta = uu___1;_}
        -> is_fstar_value t1
    | FStar_Syntax_Syntax.Tm_ascribed
        { FStar_Syntax_Syntax.tm = t1; FStar_Syntax_Syntax.asc = uu___1;
          FStar_Syntax_Syntax.eff_opt = uu___2;_}
        -> is_fstar_value t1
    | uu___1 -> false
let rec (is_ml_value : FStar_Extraction_ML_Syntax.mlexpr -> Prims.bool) =
  fun e ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_Const uu___ -> true
    | FStar_Extraction_ML_Syntax.MLE_Var uu___ -> true
    | FStar_Extraction_ML_Syntax.MLE_Name uu___ -> true
    | FStar_Extraction_ML_Syntax.MLE_Fun uu___ -> true
    | FStar_Extraction_ML_Syntax.MLE_CTor (uu___, exps) ->
        FStar_Compiler_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Tuple exps ->
        FStar_Compiler_Util.for_all is_ml_value exps
    | FStar_Extraction_ML_Syntax.MLE_Record (uu___, fields) ->
        FStar_Compiler_Util.for_all
          (fun uu___1 -> match uu___1 with | (uu___2, e1) -> is_ml_value e1)
          fields
    | FStar_Extraction_ML_Syntax.MLE_TApp (h, uu___) -> is_ml_value h
    | uu___ -> false
let (normalize_abs : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t0 ->
    let rec aux bs t copt =
      let t1 = FStar_Syntax_Subst.compress t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_abs
          { FStar_Syntax_Syntax.bs = bs'; FStar_Syntax_Syntax.body = body;
            FStar_Syntax_Syntax.rc_opt = copt1;_}
          -> aux (FStar_Compiler_List.op_At bs bs') body copt1
      | uu___ ->
          let e' = FStar_Syntax_Util.unascribe t1 in
          let uu___1 = FStar_Syntax_Util.is_fun e' in
          if uu___1 then aux bs e' copt else FStar_Syntax_Util.abs bs e' copt in
    aux [] t0 FStar_Pervasives_Native.None
let (unit_binder : unit -> FStar_Syntax_Syntax.binder) =
  fun uu___ ->
    let uu___1 =
      FStar_Syntax_Syntax.new_bv FStar_Pervasives_Native.None
        FStar_Syntax_Syntax.t_unit in
    FStar_Compiler_Effect.op_Less_Bar FStar_Syntax_Syntax.mk_binder uu___1
let (check_pats_for_ite :
  (FStar_Syntax_Syntax.pat * FStar_Syntax_Syntax.term
    FStar_Pervasives_Native.option * FStar_Syntax_Syntax.term) Prims.list ->
    (Prims.bool * FStar_Syntax_Syntax.term FStar_Pervasives_Native.option *
      FStar_Syntax_Syntax.term FStar_Pervasives_Native.option))
  =
  fun l ->
    let def =
      (false, FStar_Pervasives_Native.None, FStar_Pervasives_Native.None) in
    if (FStar_Compiler_List.length l) <> (Prims.of_int (2))
    then def
    else
      (let uu___1 = FStar_Compiler_List.hd l in
       match uu___1 with
       | (p1, w1, e1) ->
           let uu___2 =
             let uu___3 = FStar_Compiler_List.tl l in
             FStar_Compiler_List.hd uu___3 in
           (match uu___2 with
            | (p2, w2, e2) ->
                (match (w1, w2, (p1.FStar_Syntax_Syntax.v),
                         (p2.FStar_Syntax_Syntax.v))
                 with
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None,
                    FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool
                    (true)), FStar_Syntax_Syntax.Pat_constant
                    (FStar_Const.Const_bool (false))) ->
                     (true, (FStar_Pervasives_Native.Some e1),
                       (FStar_Pervasives_Native.Some e2))
                 | (FStar_Pervasives_Native.None,
                    FStar_Pervasives_Native.None,
                    FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_bool
                    (false)), FStar_Syntax_Syntax.Pat_constant
                    (FStar_Const.Const_bool (true))) ->
                     (true, (FStar_Pervasives_Native.Some e2),
                       (FStar_Pervasives_Native.Some e1))
                 | uu___3 -> def)))
let (instantiate_tyscheme :
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty)
  = fun s -> fun args -> FStar_Extraction_ML_Util.subst s args
let (fresh_mlidents :
  FStar_Extraction_ML_Syntax.mlty Prims.list ->
    FStar_Extraction_ML_UEnv.uenv ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun ts ->
    fun g ->
      let uu___ =
        FStar_Compiler_List.fold_right
          (fun t ->
             fun uu___1 ->
               match uu___1 with
               | (uenv, vs) ->
                   let uu___2 = FStar_Extraction_ML_UEnv.new_mlident uenv in
                   (match uu___2 with | (uenv1, v) -> (uenv1, ((v, t) :: vs))))
          ts (g, []) in
      match uu___ with | (g1, vs_ts) -> (vs_ts, g1)
let (instantiate_maybe_partial :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlexpr ->
      FStar_Extraction_ML_Syntax.mltyscheme ->
        FStar_Extraction_ML_Syntax.mlty Prims.list ->
          (FStar_Extraction_ML_Syntax.mlexpr *
            FStar_Extraction_ML_Syntax.e_tag *
            FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun e ->
      fun s ->
        fun tyargs ->
          let uu___ = s in
          match uu___ with
          | (vars, t) ->
              let n_vars = FStar_Compiler_List.length vars in
              let n_args = FStar_Compiler_List.length tyargs in
              if n_args = n_vars
              then
                (if n_args = Prims.int_zero
                 then (e, FStar_Extraction_ML_Syntax.E_PURE, t)
                 else
                   (let ts = instantiate_tyscheme (vars, t) tyargs in
                    let tapp =
                      {
                        FStar_Extraction_ML_Syntax.expr =
                          (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs));
                        FStar_Extraction_ML_Syntax.mlty = ts;
                        FStar_Extraction_ML_Syntax.loc =
                          (e.FStar_Extraction_ML_Syntax.loc)
                      } in
                    (tapp, FStar_Extraction_ML_Syntax.E_PURE, ts)))
              else
                if n_args < n_vars
                then
                  (let extra_tyargs =
                     let uu___2 = FStar_Compiler_Util.first_N n_args vars in
                     match uu___2 with
                     | (uu___3, rest_vars) ->
                         FStar_Compiler_Effect.op_Bar_Greater rest_vars
                           (FStar_Compiler_List.map
                              (fun uu___4 ->
                                 FStar_Extraction_ML_Syntax.MLTY_Erased)) in
                   let tyargs1 =
                     FStar_Compiler_List.op_At tyargs extra_tyargs in
                   let ts = instantiate_tyscheme (vars, t) tyargs1 in
                   let tapp =
                     {
                       FStar_Extraction_ML_Syntax.expr =
                         (FStar_Extraction_ML_Syntax.MLE_TApp (e, tyargs1));
                       FStar_Extraction_ML_Syntax.mlty = ts;
                       FStar_Extraction_ML_Syntax.loc =
                         (e.FStar_Extraction_ML_Syntax.loc)
                     } in
                   let t1 =
                     FStar_Compiler_List.fold_left
                       (fun out ->
                          fun t2 ->
                            FStar_Extraction_ML_Syntax.MLTY_Fun
                              (t2, FStar_Extraction_ML_Syntax.E_PURE, out))
                       ts extra_tyargs in
                   let uu___2 = fresh_mlidents extra_tyargs g in
                   match uu___2 with
                   | (vs_ts, g1) ->
                       let f =
                         FStar_Compiler_Effect.op_Less_Bar
                           (FStar_Extraction_ML_Syntax.with_ty t1)
                           (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, tapp)) in
                       (f, FStar_Extraction_ML_Syntax.E_PURE, t1))
                else
                  failwith
                    "Impossible: instantiate_maybe_partial called with too many arguments"
let (eta_expand :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun t ->
      fun e ->
        let uu___ = FStar_Extraction_ML_Util.doms_and_cod t in
        match uu___ with
        | (ts, r) ->
            if ts = []
            then e
            else
              (let uu___2 = fresh_mlidents ts g in
               match uu___2 with
               | (vs_ts, g1) ->
                   let vs_es =
                     FStar_Compiler_List.map
                       (fun uu___3 ->
                          match uu___3 with
                          | (v, t1) ->
                              FStar_Extraction_ML_Syntax.with_ty t1
                                (FStar_Extraction_ML_Syntax.MLE_Var v)) vs_ts in
                   let body =
                     FStar_Compiler_Effect.op_Less_Bar
                       (FStar_Extraction_ML_Syntax.with_ty r)
                       (FStar_Extraction_ML_Syntax.MLE_App (e, vs_es)) in
                   FStar_Compiler_Effect.op_Less_Bar
                     (FStar_Extraction_ML_Syntax.with_ty t)
                     (FStar_Extraction_ML_Syntax.MLE_Fun (vs_ts, body)))
let (default_value_for_ty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun t ->
      let uu___ = FStar_Extraction_ML_Util.doms_and_cod t in
      match uu___ with
      | (ts, r) ->
          let body r1 =
            let r2 =
              let uu___1 = FStar_Extraction_ML_Util.udelta_unfold g r1 in
              match uu___1 with
              | FStar_Pervasives_Native.None -> r1
              | FStar_Pervasives_Native.Some r3 -> r3 in
            match r2 with
            | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                FStar_Extraction_ML_Syntax.ml_unit
            | FStar_Extraction_ML_Syntax.MLTY_Top ->
                FStar_Extraction_ML_Syntax.apply_obj_repr
                  FStar_Extraction_ML_Syntax.ml_unit
                  FStar_Extraction_ML_Syntax.MLTY_Erased
            | uu___1 ->
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty r2)
                  (FStar_Extraction_ML_Syntax.MLE_Coerce
                     (FStar_Extraction_ML_Syntax.ml_unit,
                       FStar_Extraction_ML_Syntax.MLTY_Erased, r2)) in
          if ts = []
          then body r
          else
            (let uu___2 = fresh_mlidents ts g in
             match uu___2 with
             | (vs_ts, g1) ->
                 let uu___3 =
                   let uu___4 = let uu___5 = body r in (vs_ts, uu___5) in
                   FStar_Extraction_ML_Syntax.MLE_Fun uu___4 in
                 FStar_Compiler_Effect.op_Less_Bar
                   (FStar_Extraction_ML_Syntax.with_ty t) uu___3)
let (maybe_eta_expand_coercion :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun expect ->
      fun e ->
        let uu___ =
          let uu___1 = FStar_Options.codegen () in
          uu___1 = (FStar_Pervasives_Native.Some FStar_Options.Krml) in
        if uu___ then e else eta_expand g expect e
let (apply_coercion :
  FStar_Compiler_Range_Type.range ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlty ->
          FStar_Extraction_ML_Syntax.mlty ->
            FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun pos ->
    fun g ->
      fun e ->
        fun ty ->
          fun expect ->
            (let uu___1 = FStar_Extraction_ML_Util.codegen_fsharp () in
             if uu___1
             then
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                     FStar_Extraction_ML_Code.string_of_mlty uu___5 ty in
                   let uu___5 =
                     let uu___6 =
                       FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                     FStar_Extraction_ML_Code.string_of_mlty uu___6 expect in
                   FStar_Compiler_Util.format2
                     "Inserted an unsafe type coercion in generated code from %s to %s; this may be unsound in F#"
                     uu___4 uu___5 in
                 (FStar_Errors_Codes.Warning_NoMagicInFSharp, uu___3) in
               FStar_Errors.log_issue_text pos uu___2
             else ());
            (let mk_fun binder body =
               match body.FStar_Extraction_ML_Syntax.expr with
               | FStar_Extraction_ML_Syntax.MLE_Fun (binders, body1) ->
                   FStar_Extraction_ML_Syntax.MLE_Fun
                     ((binder :: binders), body1)
               | uu___1 ->
                   FStar_Extraction_ML_Syntax.MLE_Fun ([binder], body) in
             let rec aux e1 ty1 expect1 =
               let coerce_branch uu___1 =
                 match uu___1 with
                 | (pat, w, b) ->
                     let uu___2 = aux b ty1 expect1 in (pat, w, uu___2) in
               let rec undelta mlty =
                 let uu___1 = FStar_Extraction_ML_Util.udelta_unfold g mlty in
                 match uu___1 with
                 | FStar_Pervasives_Native.Some t -> undelta t
                 | FStar_Pervasives_Native.None -> mlty in
               let uu___1 =
                 let uu___2 = undelta expect1 in
                 ((e1.FStar_Extraction_ML_Syntax.expr), ty1, uu___2) in
               match uu___1 with
               | (FStar_Extraction_ML_Syntax.MLE_Fun (arg::rest, body),
                  FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu___2, t1),
                  FStar_Extraction_ML_Syntax.MLTY_Fun (s0, uu___3, s1)) ->
                   let body1 =
                     match rest with
                     | [] -> body
                     | uu___4 ->
                         FStar_Extraction_ML_Syntax.with_ty t1
                           (FStar_Extraction_ML_Syntax.MLE_Fun (rest, body)) in
                   let body2 = aux body1 t1 s1 in
                   let uu___4 = type_leq g s0 t0 in
                   if uu___4
                   then
                     FStar_Extraction_ML_Syntax.with_ty expect1
                       (mk_fun arg body2)
                   else
                     (let lb =
                        let uu___6 =
                          let uu___7 =
                            let uu___8 =
                              let uu___9 =
                                FStar_Compiler_Effect.op_Less_Bar
                                  (FStar_Extraction_ML_Syntax.with_ty s0)
                                  (FStar_Extraction_ML_Syntax.MLE_Var
                                     (FStar_Pervasives_Native.fst arg)) in
                              (uu___9, s0, t0) in
                            FStar_Extraction_ML_Syntax.MLE_Coerce uu___8 in
                          FStar_Extraction_ML_Syntax.with_ty t0 uu___7 in
                        {
                          FStar_Extraction_ML_Syntax.mllb_name =
                            (FStar_Pervasives_Native.fst arg);
                          FStar_Extraction_ML_Syntax.mllb_tysc =
                            (FStar_Pervasives_Native.Some ([], t0));
                          FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                          FStar_Extraction_ML_Syntax.mllb_def = uu___6;
                          FStar_Extraction_ML_Syntax.mllb_meta = [];
                          FStar_Extraction_ML_Syntax.print_typ = false
                        } in
                      let body3 =
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_Extraction_ML_Syntax.with_ty s1)
                          (FStar_Extraction_ML_Syntax.MLE_Let
                             ((FStar_Extraction_ML_Syntax.NonRec, [lb]),
                               body2)) in
                      FStar_Extraction_ML_Syntax.with_ty expect1
                        (mk_fun ((FStar_Pervasives_Native.fst arg), s0) body3))
               | (FStar_Extraction_ML_Syntax.MLE_Let (lbs, body), uu___2,
                  uu___3) ->
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = aux body ty1 expect1 in (lbs, uu___6) in
                     FStar_Extraction_ML_Syntax.MLE_Let uu___5 in
                   FStar_Compiler_Effect.op_Less_Bar
                     (FStar_Extraction_ML_Syntax.with_ty expect1) uu___4
               | (FStar_Extraction_ML_Syntax.MLE_Match (s, branches), uu___2,
                  uu___3) ->
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStar_Compiler_List.map coerce_branch branches in
                       (s, uu___6) in
                     FStar_Extraction_ML_Syntax.MLE_Match uu___5 in
                   FStar_Compiler_Effect.op_Less_Bar
                     (FStar_Extraction_ML_Syntax.with_ty expect1) uu___4
               | (FStar_Extraction_ML_Syntax.MLE_If (s, b1, b2_opt), uu___2,
                  uu___3) ->
                   let uu___4 =
                     let uu___5 =
                       let uu___6 = aux b1 ty1 expect1 in
                       let uu___7 =
                         FStar_Compiler_Util.map_opt b2_opt
                           (fun b2 -> aux b2 ty1 expect1) in
                       (s, uu___6, uu___7) in
                     FStar_Extraction_ML_Syntax.MLE_If uu___5 in
                   FStar_Compiler_Effect.op_Less_Bar
                     (FStar_Extraction_ML_Syntax.with_ty expect1) uu___4
               | (FStar_Extraction_ML_Syntax.MLE_Seq es, uu___2, uu___3) ->
                   let uu___4 = FStar_Compiler_Util.prefix es in
                   (match uu___4 with
                    | (prefix, last) ->
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 = aux last ty1 expect1 in [uu___8] in
                            FStar_Compiler_List.op_At prefix uu___7 in
                          FStar_Extraction_ML_Syntax.MLE_Seq uu___6 in
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_Extraction_ML_Syntax.with_ty expect1) uu___5)
               | (FStar_Extraction_ML_Syntax.MLE_Try (s, branches), uu___2,
                  uu___3) ->
                   let uu___4 =
                     let uu___5 =
                       let uu___6 =
                         FStar_Compiler_List.map coerce_branch branches in
                       (s, uu___6) in
                     FStar_Extraction_ML_Syntax.MLE_Try uu___5 in
                   FStar_Compiler_Effect.op_Less_Bar
                     (FStar_Extraction_ML_Syntax.with_ty expect1) uu___4
               | uu___2 ->
                   FStar_Extraction_ML_Syntax.with_ty expect1
                     (FStar_Extraction_ML_Syntax.MLE_Coerce
                        (e1, ty1, expect1)) in
             aux e ty expect)
let (maybe_coerce :
  FStar_Compiler_Range_Type.range ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Extraction_ML_Syntax.mlexpr ->
        FStar_Extraction_ML_Syntax.mlty ->
          FStar_Extraction_ML_Syntax.mlty ->
            FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun pos ->
    fun g ->
      fun e ->
        fun ty ->
          fun expect ->
            let ty1 = eraseTypeDeep g ty in
            let uu___ =
              type_leq_c g (FStar_Pervasives_Native.Some e) ty1 expect in
            match uu___ with
            | (true, FStar_Pervasives_Native.Some e') -> e'
            | uu___1 ->
                (match ty1 with
                 | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                     default_value_for_ty g expect
                 | uu___2 ->
                     let uu___3 =
                       let uu___4 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           ty1 in
                       let uu___5 =
                         FStar_Extraction_ML_Util.erase_effect_annotations
                           expect in
                       type_leq g uu___4 uu___5 in
                     if uu___3
                     then
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu___5 ->
                             let uu___6 =
                               let uu___7 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu___7 e in
                             let uu___7 =
                               let uu___8 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlty uu___8
                                 ty1 in
                             FStar_Compiler_Util.print2
                               "\n Effect mismatch on type of %s : %s\n"
                               uu___6 uu___7);
                        e)
                     else
                       (FStar_Extraction_ML_UEnv.debug g
                          (fun uu___6 ->
                             let uu___7 =
                               let uu___8 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlexpr
                                 uu___8 e in
                             let uu___8 =
                               let uu___9 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlty uu___9
                                 ty1 in
                             let uu___9 =
                               let uu___10 =
                                 FStar_Extraction_ML_UEnv.current_module_of_uenv
                                   g in
                               FStar_Extraction_ML_Code.string_of_mlty
                                 uu___10 expect in
                             FStar_Compiler_Util.print3
                               "\n (*needed to coerce expression \n %s \n of type \n %s \n to type \n %s *) \n"
                               uu___7 uu___8 uu___9);
                        (let uu___6 = apply_coercion pos g e ty1 expect in
                         maybe_eta_expand_coercion g expect uu___6)))
let (bv_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.bv -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun bv ->
      let uu___ = FStar_Extraction_ML_UEnv.lookup_bv g bv in
      match uu___ with
      | FStar_Pervasives.Inl ty_b -> ty_b.FStar_Extraction_ML_UEnv.ty_b_ty
      | uu___1 -> FStar_Extraction_ML_Syntax.MLTY_Top
let (extraction_norm_steps : FStar_TypeChecker_Env.step Prims.list) =
  let extraction_norm_steps_core =
    [FStar_TypeChecker_Env.AllowUnboundUniverses;
    FStar_TypeChecker_Env.EraseUniverses;
    FStar_TypeChecker_Env.Inlining;
    FStar_TypeChecker_Env.Eager_unfolding;
    FStar_TypeChecker_Env.Exclude FStar_TypeChecker_Env.Zeta;
    FStar_TypeChecker_Env.Primops;
    FStar_TypeChecker_Env.Unascribe;
    FStar_TypeChecker_Env.ForExtraction] in
  let extraction_norm_steps_nbe = FStar_TypeChecker_Env.NBE ::
    extraction_norm_steps_core in
  let uu___ = FStar_Options.use_nbe_for_extraction () in
  if uu___ then extraction_norm_steps_nbe else extraction_norm_steps_core
let (normalize_for_extraction :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun e ->
      let uu___ = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
      FStar_TypeChecker_Normalize.normalize extraction_norm_steps uu___ e
let maybe_reify_comp :
  'uuuuu .
    'uuuuu ->
      FStar_TypeChecker_Env.env ->
        FStar_Syntax_Syntax.comp -> FStar_Syntax_Syntax.term
  =
  fun g ->
    fun env ->
      fun c ->
        let uu___ =
          let uu___1 =
            FStar_Compiler_Effect.op_Bar_Greater c
              FStar_Syntax_Util.comp_effect_name in
          FStar_Compiler_Effect.op_Bar_Greater uu___1
            (FStar_TypeChecker_Util.effect_extraction_mode env) in
        match uu___ with
        | FStar_Syntax_Syntax.Extract_reify ->
            let uu___1 =
              FStar_TypeChecker_Env.reify_comp env c
                FStar_Syntax_Syntax.U_unknown in
            FStar_Compiler_Effect.op_Bar_Greater uu___1
              (FStar_TypeChecker_Normalize.normalize extraction_norm_steps
                 env)
        | FStar_Syntax_Syntax.Extract_primitive ->
            FStar_Syntax_Util.comp_result c
        | FStar_Syntax_Syntax.Extract_none s ->
            let uu___1 =
              FStar_Compiler_Effect.op_Bar_Greater c
                FStar_Syntax_Util.comp_effect_name in
            let uu___2 = FStar_Syntax_Print.comp_to_string c in
            err_cannot_extract_effect uu___1 c.FStar_Syntax_Syntax.pos s
              uu___2
let (maybe_reify_term :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Ident.lident -> FStar_Syntax_Syntax.term)
  =
  fun env ->
    fun t ->
      fun l ->
        let uu___ = FStar_TypeChecker_Util.effect_extraction_mode env l in
        match uu___ with
        | FStar_Syntax_Syntax.Extract_reify ->
            let uu___1 =
              FStar_Syntax_Util.mk_reify t (FStar_Pervasives_Native.Some l) in
            FStar_TypeChecker_Util.norm_reify env
              [FStar_TypeChecker_Env.Inlining;
              FStar_TypeChecker_Env.ForExtraction;
              FStar_TypeChecker_Env.Unascribe] uu___1
        | FStar_Syntax_Syntax.Extract_primitive -> t
        | FStar_Syntax_Syntax.Extract_none s ->
            let uu___1 = FStar_Syntax_Print.term_to_string t in
            err_cannot_extract_effect l t.FStar_Syntax_Syntax.pos s uu___1
let (has_extract_as_impure_effect :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.fv -> Prims.bool) =
  fun g ->
    fun fv ->
      let uu___ = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
      FStar_TypeChecker_Env.fv_has_attr uu___ fv
        FStar_Parser_Const.extract_as_impure_effect_lid
let (head_of_type_is_extract_as_impure_effect :
  FStar_Extraction_ML_UEnv.uenv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun g ->
    fun t ->
      let uu___ = FStar_Syntax_Util.head_and_args t in
      match uu___ with
      | (hd, uu___1) ->
          let uu___2 =
            let uu___3 = FStar_Syntax_Util.un_uinst hd in
            uu___3.FStar_Syntax_Syntax.n in
          (match uu___2 with
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               has_extract_as_impure_effect g fv
           | uu___3 -> false)
let rec (translate_term_to_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let arg_as_mlty g1 uu___ =
        match uu___ with
        | (a, uu___1) ->
            let uu___2 = is_type g1 a in
            if uu___2
            then translate_term_to_mlty g1 a
            else FStar_Extraction_ML_Syntax.MLTY_Erased in
      let fv_app_as_mlty g1 fv args =
        let uu___ =
          let uu___1 = FStar_Extraction_ML_UEnv.is_fv_type g1 fv in
          Prims.op_Negation uu___1 in
        if uu___
        then FStar_Extraction_ML_Syntax.MLTY_Top
        else
          (let uu___2 = has_extract_as_impure_effect g1 fv in
           if uu___2
           then
             let uu___3 = args in
             match uu___3 with
             | (a, uu___4)::uu___5 -> translate_term_to_mlty g1 a
           else
             (let uu___4 =
                let uu___5 =
                  let uu___6 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
                  FStar_TypeChecker_Env.lookup_lid uu___6
                    (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                match uu___5 with
                | ((uu___6, fvty), uu___7) ->
                    let fvty1 =
                      let uu___8 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
                      FStar_TypeChecker_Normalize.normalize
                        [FStar_TypeChecker_Env.UnfoldUntil
                           FStar_Syntax_Syntax.delta_constant;
                        FStar_TypeChecker_Env.ForExtraction] uu___8 fvty in
                    FStar_Syntax_Util.arrow_formals fvty1 in
              match uu___4 with
              | (formals, uu___5) ->
                  let mlargs = FStar_Compiler_List.map (arg_as_mlty g1) args in
                  let mlargs1 =
                    let n_args = FStar_Compiler_List.length args in
                    if (FStar_Compiler_List.length formals) > n_args
                    then
                      let uu___6 = FStar_Compiler_Util.first_N n_args formals in
                      match uu___6 with
                      | (uu___7, rest) ->
                          let uu___8 =
                            FStar_Compiler_List.map
                              (fun uu___9 ->
                                 FStar_Extraction_ML_Syntax.MLTY_Erased) rest in
                          FStar_Compiler_List.op_At mlargs uu___8
                    else mlargs in
                  let nm =
                    FStar_Extraction_ML_UEnv.mlpath_of_lident g1
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  FStar_Extraction_ML_Syntax.MLTY_Named (mlargs1, nm))) in
      let aux env t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_type uu___ ->
            FStar_Extraction_ML_Syntax.MLTY_Erased
        | FStar_Syntax_Syntax.Tm_bvar uu___ ->
            let uu___1 =
              let uu___2 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Compiler_Util.format1 "Impossible: Unexpected term %s"
                uu___2 in
            failwith uu___1
        | FStar_Syntax_Syntax.Tm_delayed uu___ ->
            let uu___1 =
              let uu___2 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Compiler_Util.format1 "Impossible: Unexpected term %s"
                uu___2 in
            failwith uu___1
        | FStar_Syntax_Syntax.Tm_unknown ->
            let uu___ =
              let uu___1 = FStar_Syntax_Print.term_to_string t1 in
              FStar_Compiler_Util.format1 "Impossible: Unexpected term %s"
                uu___1 in
            failwith uu___
        | FStar_Syntax_Syntax.Tm_lazy i ->
            let uu___ = FStar_Syntax_Util.unfold_lazy i in
            translate_term_to_mlty env uu___
        | FStar_Syntax_Syntax.Tm_constant uu___ ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_quoted uu___ ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_uvar uu___ ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_meta
            { FStar_Syntax_Syntax.tm2 = t2;
              FStar_Syntax_Syntax.meta = uu___;_}
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_refine
            {
              FStar_Syntax_Syntax.b =
                { FStar_Syntax_Syntax.ppname = uu___;
                  FStar_Syntax_Syntax.index = uu___1;
                  FStar_Syntax_Syntax.sort = t2;_};
              FStar_Syntax_Syntax.phi = uu___2;_}
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_uinst (t2, uu___) ->
            translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_ascribed
            { FStar_Syntax_Syntax.tm = t2; FStar_Syntax_Syntax.asc = uu___;
              FStar_Syntax_Syntax.eff_opt = uu___1;_}
            -> translate_term_to_mlty env t2
        | FStar_Syntax_Syntax.Tm_name bv -> bv_as_mlty env bv
        | FStar_Syntax_Syntax.Tm_fvar fv -> fv_app_as_mlty env fv []
        | FStar_Syntax_Syntax.Tm_arrow
            { FStar_Syntax_Syntax.bs1 = bs; FStar_Syntax_Syntax.comp = c;_}
            ->
            let uu___ = FStar_Syntax_Subst.open_comp bs c in
            (match uu___ with
             | (bs1, c1) ->
                 let uu___1 = binders_as_ml_binders env bs1 in
                 (match uu___1 with
                  | (mlbs, env1) ->
                      let codom =
                        let uu___2 =
                          FStar_Extraction_ML_UEnv.tcenv_of_uenv env1 in
                        maybe_reify_comp env1 uu___2 c1 in
                      let t_ret = translate_term_to_mlty env1 codom in
                      let etag =
                        effect_as_etag env1
                          (FStar_Syntax_Util.comp_effect_name c1) in
                      let etag1 =
                        if etag = FStar_Extraction_ML_Syntax.E_IMPURE
                        then etag
                        else
                          (let uu___3 =
                             head_of_type_is_extract_as_impure_effect env1
                               codom in
                           if uu___3
                           then FStar_Extraction_ML_Syntax.E_IMPURE
                           else etag) in
                      let uu___2 =
                        FStar_Compiler_List.fold_right
                          (fun uu___3 ->
                             fun uu___4 ->
                               match (uu___3, uu___4) with
                               | ((uu___5, t2), (tag, t')) ->
                                   (FStar_Extraction_ML_Syntax.E_PURE,
                                     (FStar_Extraction_ML_Syntax.MLTY_Fun
                                        (t2, tag, t')))) mlbs (etag1, t_ret) in
                      (match uu___2 with | (uu___3, t2) -> t2)))
        | FStar_Syntax_Syntax.Tm_app uu___ ->
            let uu___1 = FStar_Syntax_Util.head_and_args_full t1 in
            (match uu___1 with
             | (head, args) ->
                 let res =
                   let uu___2 =
                     let uu___3 =
                       let uu___4 = FStar_Syntax_Util.un_uinst head in
                       uu___4.FStar_Syntax_Syntax.n in
                     (uu___3, args) in
                   match uu___2 with
                   | (FStar_Syntax_Syntax.Tm_name bv, uu___3) ->
                       bv_as_mlty env bv
                   | (FStar_Syntax_Syntax.Tm_fvar fv, uu___3::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.steel_memory_inv_lid
                       ->
                       translate_term_to_mlty env FStar_Syntax_Syntax.t_unit
                   | (FStar_Syntax_Syntax.Tm_fvar fv, uu___3) ->
                       fv_app_as_mlty env fv args
                   | uu___3 -> FStar_Extraction_ML_Syntax.MLTY_Top in
                 res)
        | FStar_Syntax_Syntax.Tm_abs
            { FStar_Syntax_Syntax.bs = bs; FStar_Syntax_Syntax.body = ty;
              FStar_Syntax_Syntax.rc_opt = uu___;_}
            ->
            let uu___1 = FStar_Syntax_Subst.open_term bs ty in
            (match uu___1 with
             | (bs1, ty1) ->
                 let uu___2 = binders_as_ml_binders env bs1 in
                 (match uu___2 with
                  | (bts, env1) -> translate_term_to_mlty env1 ty1))
        | FStar_Syntax_Syntax.Tm_let uu___ ->
            FStar_Extraction_ML_Syntax.MLTY_Top
        | FStar_Syntax_Syntax.Tm_match uu___ ->
            FStar_Extraction_ML_Syntax.MLTY_Top in
      let rec is_top_ty t =
        match t with
        | FStar_Extraction_ML_Syntax.MLTY_Top -> true
        | FStar_Extraction_ML_Syntax.MLTY_Named uu___ ->
            let uu___1 = FStar_Extraction_ML_Util.udelta_unfold g t in
            (match uu___1 with
             | FStar_Pervasives_Native.None -> false
             | FStar_Pervasives_Native.Some t1 -> is_top_ty t1)
        | uu___ -> false in
      let uu___ =
        let uu___1 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
        FStar_TypeChecker_Util.must_erase_for_extraction uu___1 t0 in
      if uu___
      then FStar_Extraction_ML_Syntax.MLTY_Erased
      else
        (let mlt = aux g t0 in
         let uu___2 = is_top_ty mlt in
         if uu___2 then FStar_Extraction_ML_Syntax.MLTY_Top else mlt)
and (binders_as_ml_binders :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.binders ->
      ((FStar_Extraction_ML_Syntax.mlident * FStar_Extraction_ML_Syntax.mlty)
        Prims.list * FStar_Extraction_ML_UEnv.uenv))
  =
  fun g ->
    fun bs ->
      let uu___ =
        FStar_Compiler_Effect.op_Bar_Greater bs
          (FStar_Compiler_List.fold_left
             (fun uu___1 ->
                fun b ->
                  match uu___1 with
                  | (ml_bs, env) ->
                      let uu___2 = is_type_binder g b in
                      if uu___2
                      then
                        let b1 = b.FStar_Syntax_Syntax.binder_bv in
                        let env1 =
                          FStar_Extraction_ML_UEnv.extend_ty env b1 true in
                        let ml_b =
                          let uu___3 =
                            FStar_Extraction_ML_UEnv.lookup_ty env1 b1 in
                          uu___3.FStar_Extraction_ML_UEnv.ty_b_name in
                        let ml_b1 =
                          (ml_b, FStar_Extraction_ML_Syntax.ml_unit_ty) in
                        ((ml_b1 :: ml_bs), env1)
                      else
                        (let b1 = b.FStar_Syntax_Syntax.binder_bv in
                         let t =
                           translate_term_to_mlty env
                             b1.FStar_Syntax_Syntax.sort in
                         let uu___4 =
                           FStar_Extraction_ML_UEnv.extend_bv env b1 
                             ([], t) false false in
                         match uu___4 with
                         | (env1, b2, uu___5) ->
                             let ml_b = (b2, t) in ((ml_b :: ml_bs), env1)))
             ([], g)) in
      match uu___ with
      | (ml_bs, env) -> ((FStar_Compiler_List.rev ml_bs), env)
let (term_as_mlty :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlty)
  =
  fun g ->
    fun t0 ->
      let t =
        let uu___ = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
        FStar_TypeChecker_Normalize.normalize extraction_norm_steps uu___ t0 in
      translate_term_to_mlty g t
let (mk_MLE_Seq :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun e1 ->
    fun e2 ->
      match ((e1.FStar_Extraction_ML_Syntax.expr),
              (e2.FStar_Extraction_ML_Syntax.expr))
      with
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1,
         FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq
            (FStar_Compiler_List.op_At es1 es2)
      | (FStar_Extraction_ML_Syntax.MLE_Seq es1, uu___) ->
          FStar_Extraction_ML_Syntax.MLE_Seq
            (FStar_Compiler_List.op_At es1 [e2])
      | (uu___, FStar_Extraction_ML_Syntax.MLE_Seq es2) ->
          FStar_Extraction_ML_Syntax.MLE_Seq (e1 :: es2)
      | uu___ -> FStar_Extraction_ML_Syntax.MLE_Seq [e1; e2]
let (mk_MLE_Let :
  Prims.bool ->
    FStar_Extraction_ML_Syntax.mlletbinding ->
      FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr')
  =
  fun top_level ->
    fun lbs ->
      fun body ->
        match lbs with
        | (FStar_Extraction_ML_Syntax.NonRec, lb::[]) when
            Prims.op_Negation top_level ->
            (match lb.FStar_Extraction_ML_Syntax.mllb_tysc with
             | FStar_Pervasives_Native.Some ([], t) when
                 t = FStar_Extraction_ML_Syntax.ml_unit_ty ->
                 if
                   body.FStar_Extraction_ML_Syntax.expr =
                     FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                 then
                   (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                 else
                   (match body.FStar_Extraction_ML_Syntax.expr with
                    | FStar_Extraction_ML_Syntax.MLE_Var x when
                        x = lb.FStar_Extraction_ML_Syntax.mllb_name ->
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                    | uu___1 when
                        (lb.FStar_Extraction_ML_Syntax.mllb_def).FStar_Extraction_ML_Syntax.expr
                          =
                          FStar_Extraction_ML_Syntax.ml_unit.FStar_Extraction_ML_Syntax.expr
                        -> body.FStar_Extraction_ML_Syntax.expr
                    | uu___1 ->
                        mk_MLE_Seq lb.FStar_Extraction_ML_Syntax.mllb_def
                          body)
             | uu___ -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body))
        | uu___ -> FStar_Extraction_ML_Syntax.MLE_Let (lbs, body)
let record_fields :
  'a .
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Ident.lident ->
        FStar_Ident.ident Prims.list ->
          'a Prims.list ->
            (FStar_Extraction_ML_Syntax.mlsymbol * 'a) Prims.list
  =
  fun g ->
    fun ty ->
      fun fns ->
        fun xs ->
          let fns1 =
            FStar_Compiler_List.map
              (fun x ->
                 FStar_Extraction_ML_UEnv.lookup_record_field_name g (ty, x))
              fns in
          FStar_Compiler_List.map2
            (fun uu___ -> fun x -> match uu___ with | (p, s) -> (s, x)) fns1
            xs
let (resugar_pat :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlpattern ->
        FStar_Extraction_ML_Syntax.mlpattern)
  =
  fun g ->
    fun q ->
      fun p ->
        match p with
        | FStar_Extraction_ML_Syntax.MLP_CTor (d, pats) ->
            let uu___ = FStar_Extraction_ML_Util.is_xtuple d in
            (match uu___ with
             | FStar_Pervasives_Native.Some n ->
                 FStar_Extraction_ML_Syntax.MLP_Tuple pats
             | uu___1 ->
                 (match q with
                  | FStar_Pervasives_Native.Some
                      (FStar_Syntax_Syntax.Record_ctor (ty, fns)) ->
                      let path =
                        let uu___2 = FStar_Ident.ns_of_lid ty in
                        FStar_Compiler_List.map FStar_Ident.string_of_id
                          uu___2 in
                      let fs = record_fields g ty fns pats in
                      let path1 =
                        FStar_Extraction_ML_UEnv.no_fstar_stubs_ns path in
                      FStar_Extraction_ML_Syntax.MLP_Record (path1, fs)
                  | uu___2 -> p))
        | uu___ -> p
let rec (extract_one_pat :
  Prims.bool ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.pat ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_UEnv.uenv ->
             FStar_Syntax_Syntax.term ->
               (FStar_Extraction_ML_Syntax.mlexpr *
                 FStar_Extraction_ML_Syntax.e_tag *
                 FStar_Extraction_ML_Syntax.mlty))
            ->
            (FStar_Extraction_ML_UEnv.uenv *
              (FStar_Extraction_ML_Syntax.mlpattern *
              FStar_Extraction_ML_Syntax.mlexpr Prims.list)
              FStar_Pervasives_Native.option * Prims.bool))
  =
  fun imp ->
    fun g ->
      fun p ->
        fun expected_ty ->
          fun term_as_mlexpr ->
            let ok t =
              match expected_ty with
              | FStar_Extraction_ML_Syntax.MLTY_Top -> false
              | uu___ ->
                  let ok1 = type_leq g t expected_ty in
                  (if Prims.op_Negation ok1
                   then
                     FStar_Extraction_ML_UEnv.debug g
                       (fun uu___2 ->
                          let uu___3 =
                            let uu___4 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g in
                            FStar_Extraction_ML_Code.string_of_mlty uu___4
                              expected_ty in
                          let uu___4 =
                            let uu___5 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g in
                            FStar_Extraction_ML_Code.string_of_mlty uu___5 t in
                          FStar_Compiler_Util.print2
                            "Expected pattern type %s; got pattern type %s\n"
                            uu___3 uu___4)
                   else ();
                   ok1) in
            match p.FStar_Syntax_Syntax.v with
            | FStar_Syntax_Syntax.Pat_constant (FStar_Const.Const_int
                (c, swopt)) when
                let uu___ = FStar_Options.codegen () in
                uu___ <> (FStar_Pervasives_Native.Some FStar_Options.Krml) ->
                let uu___ =
                  match swopt with
                  | FStar_Pervasives_Native.None ->
                      let uu___1 =
                        let uu___2 =
                          let uu___3 =
                            FStar_Extraction_ML_Util.mlconst_of_const
                              p.FStar_Syntax_Syntax.p
                              (FStar_Const.Const_int
                                 (c, FStar_Pervasives_Native.None)) in
                          FStar_Extraction_ML_Syntax.MLE_Const uu___3 in
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.ml_int_ty) uu___2 in
                      (uu___1, FStar_Extraction_ML_Syntax.ml_int_ty)
                  | FStar_Pervasives_Native.Some sw ->
                      let source_term =
                        let uu___1 =
                          let uu___2 =
                            FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                          uu___2.FStar_TypeChecker_Env.dsenv in
                        FStar_ToSyntax_ToSyntax.desugar_machine_integer
                          uu___1 c sw FStar_Compiler_Range_Type.dummyRange in
                      let uu___1 = term_as_mlexpr g source_term in
                      (match uu___1 with
                       | (mlterm, uu___2, mlty) -> (mlterm, mlty)) in
                (match uu___ with
                 | (mlc, ml_ty) ->
                     let uu___1 = FStar_Extraction_ML_UEnv.new_mlident g in
                     (match uu___1 with
                      | (g1, x) ->
                          let x_exp =
                            let x_exp1 =
                              FStar_Compiler_Effect.op_Less_Bar
                                (FStar_Extraction_ML_Syntax.with_ty
                                   expected_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Var x) in
                            let coerce x1 =
                              FStar_Compiler_Effect.op_Less_Bar
                                (FStar_Extraction_ML_Syntax.with_ty ml_ty)
                                (FStar_Extraction_ML_Syntax.MLE_Coerce
                                   (x1, ml_ty, expected_ty)) in
                            match expected_ty with
                            | FStar_Extraction_ML_Syntax.MLTY_Top ->
                                coerce x_exp1
                            | uu___2 ->
                                let uu___3 = ok ml_ty in
                                if uu___3 then x_exp1 else coerce x_exp1 in
                          let when_clause =
                            FStar_Compiler_Effect.op_Less_Bar
                              (FStar_Extraction_ML_Syntax.with_ty
                                 FStar_Extraction_ML_Syntax.ml_bool_ty)
                              (FStar_Extraction_ML_Syntax.MLE_App
                                 (FStar_Extraction_ML_Util.prims_op_equality,
                                   [x_exp; mlc])) in
                          let uu___2 = ok ml_ty in
                          (g1,
                            (FStar_Pervasives_Native.Some
                               ((FStar_Extraction_ML_Syntax.MLP_Var x),
                                 [when_clause])), uu___2)))
            | FStar_Syntax_Syntax.Pat_constant s ->
                let t =
                  let uu___ = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                  FStar_TypeChecker_TcTerm.tc_constant uu___
                    FStar_Compiler_Range_Type.dummyRange s in
                let mlty = term_as_mlty g t in
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      let uu___3 =
                        FStar_Extraction_ML_Util.mlconst_of_const
                          p.FStar_Syntax_Syntax.p s in
                      FStar_Extraction_ML_Syntax.MLP_Const uu___3 in
                    (uu___2, []) in
                  FStar_Pervasives_Native.Some uu___1 in
                let uu___1 = ok mlty in (g, uu___, uu___1)
            | FStar_Syntax_Syntax.Pat_var x ->
                let uu___ =
                  FStar_Extraction_ML_UEnv.extend_bv g x ([], expected_ty)
                    false imp in
                (match uu___ with
                 | (g1, x1, uu___1) ->
                     (g1,
                       (if imp
                        then FStar_Pervasives_Native.None
                        else
                          FStar_Pervasives_Native.Some
                            ((FStar_Extraction_ML_Syntax.MLP_Var x1), [])),
                       true))
            | FStar_Syntax_Syntax.Pat_dot_term uu___ ->
                (g, FStar_Pervasives_Native.None, true)
            | FStar_Syntax_Syntax.Pat_cons (f, uu___, pats) ->
                let uu___1 =
                  let uu___2 =
                    FStar_Extraction_ML_UEnv.try_lookup_fv
                      p.FStar_Syntax_Syntax.p g f in
                  match uu___2 with
                  | FStar_Pervasives_Native.Some
                      { FStar_Extraction_ML_UEnv.exp_b_name = uu___3;
                        FStar_Extraction_ML_UEnv.exp_b_expr =
                          {
                            FStar_Extraction_ML_Syntax.expr =
                              FStar_Extraction_ML_Syntax.MLE_Name n;
                            FStar_Extraction_ML_Syntax.mlty = uu___4;
                            FStar_Extraction_ML_Syntax.loc = uu___5;_};
                        FStar_Extraction_ML_UEnv.exp_b_tscheme = ttys;_}
                      -> (n, ttys)
                  | FStar_Pervasives_Native.Some uu___3 ->
                      failwith "Expected a constructor"
                  | FStar_Pervasives_Native.None ->
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Print.fv_to_string f in
                          FStar_Compiler_Util.format1
                            "Cannot extract this pattern, the %s constructor was erased"
                            uu___5 in
                        (FStar_Errors_Codes.Error_ErasedCtor, uu___4) in
                      FStar_Errors.raise_error uu___3
                        (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.p in
                (match uu___1 with
                 | (d, tys) ->
                     let nTyVars =
                       FStar_Compiler_List.length
                         (FStar_Pervasives_Native.fst tys) in
                     let uu___2 = FStar_Compiler_Util.first_N nTyVars pats in
                     (match uu___2 with
                      | (tysVarPats, restPats) ->
                          let f_ty =
                            let mlty_args =
                              FStar_Compiler_Effect.op_Bar_Greater tysVarPats
                                (FStar_Compiler_List.map
                                   (fun uu___3 ->
                                      match uu___3 with
                                      | (p1, uu___4) ->
                                          (match expected_ty with
                                           | FStar_Extraction_ML_Syntax.MLTY_Top
                                               ->
                                               FStar_Extraction_ML_Syntax.MLTY_Top
                                           | uu___5 ->
                                               (match p1.FStar_Syntax_Syntax.v
                                                with
                                                | FStar_Syntax_Syntax.Pat_dot_term
                                                    (FStar_Pervasives_Native.Some
                                                    t) -> term_as_mlty g t
                                                | uu___6 ->
                                                    FStar_Extraction_ML_Syntax.MLTY_Top)))) in
                            let f_ty1 =
                              FStar_Extraction_ML_Util.subst tys mlty_args in
                            FStar_Extraction_ML_Util.uncurry_mlty_fun f_ty1 in
                          (FStar_Extraction_ML_UEnv.debug g
                             (fun uu___4 ->
                                let uu___5 =
                                  FStar_Syntax_Print.fv_to_string f in
                                let uu___6 =
                                  let uu___7 = f_ty in
                                  match uu___7 with
                                  | (args, t) ->
                                      let args1 =
                                        let uu___8 =
                                          let uu___9 =
                                            let uu___10 =
                                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                                g in
                                            FStar_Extraction_ML_Code.string_of_mlty
                                              uu___10 in
                                          FStar_Compiler_List.map uu___9 args in
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          uu___8 (FStar_String.concat " -> ") in
                                      let res =
                                        let uu___8 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu___8 t in
                                      FStar_Compiler_Util.format2 "%s -> %s"
                                        args1 res in
                                FStar_Compiler_Util.print2
                                  "@@@Expected type of pattern with head = %s is %s\n"
                                  uu___5 uu___6);
                           (let uu___4 =
                              FStar_Compiler_Util.fold_map
                                (fun g1 ->
                                   fun uu___5 ->
                                     match uu___5 with
                                     | (p1, imp1) ->
                                         let uu___6 =
                                           extract_one_pat true g1 p1
                                             FStar_Extraction_ML_Syntax.MLTY_Top
                                             term_as_mlexpr in
                                         (match uu___6 with
                                          | (g2, p2, uu___7) -> (g2, p2))) g
                                tysVarPats in
                            match uu___4 with
                            | (g1, tyMLPats) ->
                                let uu___5 =
                                  FStar_Compiler_Util.fold_map
                                    (fun uu___6 ->
                                       fun uu___7 ->
                                         match (uu___6, uu___7) with
                                         | ((g2, f_ty1, ok1), (p1, imp1)) ->
                                             let uu___8 =
                                               match f_ty1 with
                                               | (hd::rest, res) ->
                                                   ((rest, res), hd)
                                               | uu___9 ->
                                                   (([],
                                                      FStar_Extraction_ML_Syntax.MLTY_Top),
                                                     FStar_Extraction_ML_Syntax.MLTY_Top) in
                                             (match uu___8 with
                                              | (f_ty2, expected_arg_ty) ->
                                                  let uu___9 =
                                                    extract_one_pat false g2
                                                      p1 expected_arg_ty
                                                      term_as_mlexpr in
                                                  (match uu___9 with
                                                   | (g3, p2, ok') ->
                                                       ((g3, f_ty2,
                                                          (ok1 && ok')), p2))))
                                    (g1, f_ty, true) restPats in
                                (match uu___5 with
                                 | ((g2, f_ty1, sub_pats_ok), restMLPats) ->
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_Compiler_Effect.op_Bar_Greater
                                           (FStar_Compiler_List.append
                                              tyMLPats restMLPats)
                                           (FStar_Compiler_List.collect
                                              (fun uu___8 ->
                                                 match uu___8 with
                                                 | FStar_Pervasives_Native.Some
                                                     x -> [x]
                                                 | uu___9 -> [])) in
                                       FStar_Compiler_Effect.op_Bar_Greater
                                         uu___7 FStar_Compiler_List.split in
                                     (match uu___6 with
                                      | (mlPats, when_clauses) ->
                                          let pat_ty_compat =
                                            match f_ty1 with
                                            | ([], t) -> ok t
                                            | uu___7 -> false in
                                          let uu___7 =
                                            let uu___8 =
                                              let uu___9 =
                                                resugar_pat g2
                                                  f.FStar_Syntax_Syntax.fv_qual
                                                  (FStar_Extraction_ML_Syntax.MLP_CTor
                                                     (d, mlPats)) in
                                              let uu___10 =
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  when_clauses
                                                  FStar_Compiler_List.flatten in
                                              (uu___9, uu___10) in
                                            FStar_Pervasives_Native.Some
                                              uu___8 in
                                          (g2, uu___7,
                                            (sub_pats_ok && pat_ty_compat))))))))
let (extract_pat :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.pat ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_UEnv.uenv ->
           FStar_Syntax_Syntax.term ->
             (FStar_Extraction_ML_Syntax.mlexpr *
               FStar_Extraction_ML_Syntax.e_tag *
               FStar_Extraction_ML_Syntax.mlty))
          ->
          (FStar_Extraction_ML_UEnv.uenv *
            (FStar_Extraction_ML_Syntax.mlpattern *
            FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option)
            Prims.list * Prims.bool))
  =
  fun g ->
    fun p ->
      fun expected_t ->
        fun term_as_mlexpr ->
          let extract_one_pat1 g1 p1 expected_t1 =
            let uu___ =
              extract_one_pat false g1 p1 expected_t1 term_as_mlexpr in
            match uu___ with
            | (g2, FStar_Pervasives_Native.Some (x, v), b) -> (g2, (x, v), b)
            | uu___1 -> failwith "Impossible: Unable to translate pattern" in
          let mk_when_clause whens =
            match whens with
            | [] -> FStar_Pervasives_Native.None
            | hd::tl ->
                let uu___ =
                  FStar_Compiler_List.fold_left
                    FStar_Extraction_ML_Util.conjoin hd tl in
                FStar_Pervasives_Native.Some uu___ in
          let uu___ = extract_one_pat1 g p expected_t in
          match uu___ with
          | (g1, (p1, whens), b) ->
              let when_clause = mk_when_clause whens in
              (g1, [(p1, when_clause)], b)
let (maybe_eta_data_and_project_record :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.fv_qual FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlexpr ->
          FStar_Extraction_ML_Syntax.mlexpr)
  =
  fun g ->
    fun qual ->
      fun residualType ->
        fun mlAppExpr ->
          let rec eta_args g1 more_args t =
            match t with
            | FStar_Extraction_ML_Syntax.MLTY_Fun (t0, uu___, t1) ->
                let uu___1 = FStar_Extraction_ML_UEnv.new_mlident g1 in
                (match uu___1 with
                 | (g2, x) ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 =
                           FStar_Compiler_Effect.op_Less_Bar
                             (FStar_Extraction_ML_Syntax.with_ty t0)
                             (FStar_Extraction_ML_Syntax.MLE_Var x) in
                         ((x, t0), uu___4) in
                       uu___3 :: more_args in
                     eta_args g2 uu___2 t1)
            | FStar_Extraction_ML_Syntax.MLTY_Named (uu___, uu___1) ->
                ((FStar_Compiler_List.rev more_args), t)
            | uu___ ->
                let uu___1 =
                  let uu___2 =
                    let uu___3 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1 in
                    FStar_Extraction_ML_Code.string_of_mlexpr uu___3
                      mlAppExpr in
                  let uu___3 =
                    let uu___4 =
                      FStar_Extraction_ML_UEnv.current_module_of_uenv g1 in
                    FStar_Extraction_ML_Code.string_of_mlty uu___4 t in
                  FStar_Compiler_Util.format2
                    "Impossible: Head type is not an arrow: (%s : %s)" uu___2
                    uu___3 in
                failwith uu___1 in
          let as_record qual1 e =
            match ((e.FStar_Extraction_ML_Syntax.expr), qual1) with
            | (FStar_Extraction_ML_Syntax.MLE_CTor (uu___, args),
               FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
               (tyname, fields))) ->
                let path =
                  let uu___1 = FStar_Ident.ns_of_lid tyname in
                  FStar_Compiler_List.map FStar_Ident.string_of_id uu___1 in
                let fields1 = record_fields g tyname fields args in
                let path1 = FStar_Extraction_ML_UEnv.no_fstar_stubs_ns path in
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty
                     e.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_Record (path1, fields1))
            | uu___ -> e in
          let resugar_and_maybe_eta qual1 e =
            let uu___ = eta_args g [] residualType in
            match uu___ with
            | (eargs, tres) ->
                (match eargs with
                 | [] ->
                     let uu___1 = as_record qual1 e in
                     FStar_Extraction_ML_Util.resugar_exp uu___1
                 | uu___1 ->
                     let uu___2 = FStar_Compiler_List.unzip eargs in
                     (match uu___2 with
                      | (binders, eargs1) ->
                          (match e.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_CTor (head, args)
                               ->
                               let body =
                                 let uu___3 =
                                   let uu___4 =
                                     FStar_Compiler_Effect.op_Less_Bar
                                       (FStar_Extraction_ML_Syntax.with_ty
                                          tres)
                                       (FStar_Extraction_ML_Syntax.MLE_CTor
                                          (head,
                                            (FStar_Compiler_List.op_At args
                                               eargs1))) in
                                   FStar_Compiler_Effect.op_Less_Bar
                                     (as_record qual1) uu___4 in
                                 FStar_Compiler_Effect.op_Less_Bar
                                   FStar_Extraction_ML_Util.resugar_exp
                                   uu___3 in
                               FStar_Compiler_Effect.op_Less_Bar
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    e.FStar_Extraction_ML_Syntax.mlty)
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    (binders, body))
                           | uu___3 ->
                               failwith "Impossible: Not a constructor"))) in
          match ((mlAppExpr.FStar_Extraction_ML_Syntax.expr), qual) with
          | (uu___, FStar_Pervasives_Native.None) -> mlAppExpr
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu___;
                FStar_Extraction_ML_Syntax.loc = uu___1;_},
              mle::args),
             FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname, f))) ->
              let fn =
                let uu___2 =
                  let uu___3 =
                    let uu___4 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Env.typ_of_datacon uu___4 constrname in
                  (uu___3, f) in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g uu___2 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu___2 ->
                    let uu___3 =
                      let uu___4 =
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu___4, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu___3 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu___;
                     FStar_Extraction_ML_Syntax.loc = uu___1;_},
                   uu___2);
                FStar_Extraction_ML_Syntax.mlty = uu___3;
                FStar_Extraction_ML_Syntax.loc = uu___4;_},
              mle::args),
             FStar_Pervasives_Native.Some
             (FStar_Syntax_Syntax.Record_projector (constrname, f))) ->
              let fn =
                let uu___5 =
                  let uu___6 =
                    let uu___7 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Env.typ_of_datacon uu___7 constrname in
                  (uu___6, f) in
                FStar_Extraction_ML_UEnv.lookup_record_field_name g uu___5 in
              let proj = FStar_Extraction_ML_Syntax.MLE_Proj (mle, fn) in
              let e =
                match args with
                | [] -> proj
                | uu___5 ->
                    let uu___6 =
                      let uu___7 =
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) proj in
                      (uu___7, args) in
                    FStar_Extraction_ML_Syntax.MLE_App uu___6 in
              FStar_Extraction_ML_Syntax.with_ty
                mlAppExpr.FStar_Extraction_ML_Syntax.mlty e
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu___;
                FStar_Extraction_ML_Syntax.loc = uu___1;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu___2 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_Compiler_Effect.op_Less_Bar (resugar_and_maybe_eta qual)
                uu___2
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu___;
                FStar_Extraction_ML_Syntax.loc = uu___1;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu___2)) ->
              let uu___3 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_Compiler_Effect.op_Less_Bar (resugar_and_maybe_eta qual)
                uu___3
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu___;
                     FStar_Extraction_ML_Syntax.loc = uu___1;_},
                   uu___2);
                FStar_Extraction_ML_Syntax.mlty = uu___3;
                FStar_Extraction_ML_Syntax.loc = uu___4;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu___5 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_Compiler_Effect.op_Less_Bar (resugar_and_maybe_eta qual)
                uu___5
          | (FStar_Extraction_ML_Syntax.MLE_App
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_TApp
                  ({
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Name mlp;
                     FStar_Extraction_ML_Syntax.mlty = uu___;
                     FStar_Extraction_ML_Syntax.loc = uu___1;_},
                   uu___2);
                FStar_Extraction_ML_Syntax.mlty = uu___3;
                FStar_Extraction_ML_Syntax.loc = uu___4;_},
              mlargs),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu___5)) ->
              let uu___6 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, mlargs)) in
              FStar_Compiler_Effect.op_Less_Bar (resugar_and_maybe_eta qual)
                uu___6
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu___ =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_Compiler_Effect.op_Less_Bar (resugar_and_maybe_eta qual)
                uu___
          | (FStar_Extraction_ML_Syntax.MLE_Name mlp,
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu___)) ->
              let uu___1 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_Compiler_Effect.op_Less_Bar (resugar_and_maybe_eta qual)
                uu___1
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu___;
                FStar_Extraction_ML_Syntax.loc = uu___1;_},
              uu___2),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Data_ctor)) ->
              let uu___3 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_Compiler_Effect.op_Less_Bar (resugar_and_maybe_eta qual)
                uu___3
          | (FStar_Extraction_ML_Syntax.MLE_TApp
             ({
                FStar_Extraction_ML_Syntax.expr =
                  FStar_Extraction_ML_Syntax.MLE_Name mlp;
                FStar_Extraction_ML_Syntax.mlty = uu___;
                FStar_Extraction_ML_Syntax.loc = uu___1;_},
              uu___2),
             FStar_Pervasives_Native.Some (FStar_Syntax_Syntax.Record_ctor
             uu___3)) ->
              let uu___4 =
                FStar_Compiler_Effect.op_Less_Bar
                  (FStar_Extraction_ML_Syntax.with_ty
                     mlAppExpr.FStar_Extraction_ML_Syntax.mlty)
                  (FStar_Extraction_ML_Syntax.MLE_CTor (mlp, [])) in
              FStar_Compiler_Effect.op_Less_Bar (resugar_and_maybe_eta qual)
                uu___4
          | uu___ -> mlAppExpr
let (maybe_promote_effect :
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.mlty ->
        (FStar_Extraction_ML_Syntax.mlexpr *
          FStar_Extraction_ML_Syntax.e_tag))
  =
  fun ml_e ->
    fun tag ->
      fun t ->
        match (tag, t) with
        | (FStar_Extraction_ML_Syntax.E_ERASABLE,
           FStar_Extraction_ML_Syntax.MLTY_Erased) ->
            (FStar_Extraction_ML_Syntax.ml_unit,
              FStar_Extraction_ML_Syntax.E_PURE)
        | (FStar_Extraction_ML_Syntax.E_PURE,
           FStar_Extraction_ML_Syntax.MLTY_Erased) ->
            (FStar_Extraction_ML_Syntax.ml_unit,
              FStar_Extraction_ML_Syntax.E_PURE)
        | uu___ -> (ml_e, tag)
let (extract_lb_sig :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.letbindings ->
      (FStar_Syntax_Syntax.lbname * FStar_Extraction_ML_Syntax.e_tag *
        (FStar_Syntax_Syntax.typ * (FStar_Syntax_Syntax.binders *
        FStar_Extraction_ML_Syntax.mltyscheme)) * Prims.bool *
        FStar_Syntax_Syntax.term) Prims.list)
  =
  fun g ->
    fun lbs ->
      let maybe_generalize uu___ =
        match uu___ with
        | { FStar_Syntax_Syntax.lbname = lbname_;
            FStar_Syntax_Syntax.lbunivs = uu___1;
            FStar_Syntax_Syntax.lbtyp = lbtyp;
            FStar_Syntax_Syntax.lbeff = lbeff;
            FStar_Syntax_Syntax.lbdef = lbdef;
            FStar_Syntax_Syntax.lbattrs = lbattrs;
            FStar_Syntax_Syntax.lbpos = uu___2;_} ->
            let f_e = effect_as_etag g lbeff in
            let lbtyp1 = FStar_Syntax_Subst.compress lbtyp in
            let no_gen uu___3 =
              let expected_t = term_as_mlty g lbtyp1 in
              (lbname_, f_e, (lbtyp1, ([], ([], expected_t))), false, lbdef) in
            let uu___3 =
              let uu___4 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
              FStar_TypeChecker_Util.must_erase_for_extraction uu___4 lbtyp1 in
            if uu___3
            then
              (lbname_, f_e,
                (lbtyp1, ([], ([], FStar_Extraction_ML_Syntax.MLTY_Erased))),
                false, lbdef)
            else
              (match lbtyp1.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_arrow
                   { FStar_Syntax_Syntax.bs1 = bs;
                     FStar_Syntax_Syntax.comp = c;_}
                   when
                   let uu___5 = FStar_Compiler_List.hd bs in
                   FStar_Compiler_Effect.op_Bar_Greater uu___5
                     (is_type_binder g)
                   ->
                   let uu___5 = FStar_Syntax_Subst.open_comp bs c in
                   (match uu___5 with
                    | (bs1, c1) ->
                        let uu___6 =
                          let uu___7 =
                            FStar_Compiler_Util.prefix_until
                              (fun x ->
                                 let uu___8 = is_type_binder g x in
                                 Prims.op_Negation uu___8) bs1 in
                          match uu___7 with
                          | FStar_Pervasives_Native.None ->
                              (bs1, (FStar_Syntax_Util.comp_result c1))
                          | FStar_Pervasives_Native.Some (bs2, b, rest) ->
                              let uu___8 =
                                FStar_Syntax_Util.arrow (b :: rest) c1 in
                              (bs2, uu___8) in
                        (match uu___6 with
                         | (tbinders, tbody) ->
                             let n_tbinders =
                               FStar_Compiler_List.length tbinders in
                             let lbdef1 =
                               let uu___7 = normalize_abs lbdef in
                               FStar_Compiler_Effect.op_Bar_Greater uu___7
                                 FStar_Syntax_Util.unmeta in
                             (match lbdef1.FStar_Syntax_Syntax.n with
                              | FStar_Syntax_Syntax.Tm_abs
                                  { FStar_Syntax_Syntax.bs = bs2;
                                    FStar_Syntax_Syntax.body = body;
                                    FStar_Syntax_Syntax.rc_opt = copt;_}
                                  ->
                                  let uu___7 =
                                    FStar_Syntax_Subst.open_term bs2 body in
                                  (match uu___7 with
                                   | (bs3, body1) ->
                                       if
                                         n_tbinders <=
                                           (FStar_Compiler_List.length bs3)
                                       then
                                         let uu___8 =
                                           FStar_Compiler_Util.first_N
                                             n_tbinders bs3 in
                                         (match uu___8 with
                                          | (targs, rest_args) ->
                                              let expected_source_ty =
                                                let s =
                                                  FStar_Compiler_List.map2
                                                    (fun uu___9 ->
                                                       fun uu___10 ->
                                                         match (uu___9,
                                                                 uu___10)
                                                         with
                                                         | ({
                                                              FStar_Syntax_Syntax.binder_bv
                                                                = x;
                                                              FStar_Syntax_Syntax.binder_qual
                                                                = uu___11;
                                                              FStar_Syntax_Syntax.binder_positivity
                                                                = uu___12;
                                                              FStar_Syntax_Syntax.binder_attrs
                                                                = uu___13;_},
                                                            {
                                                              FStar_Syntax_Syntax.binder_bv
                                                                = y;
                                                              FStar_Syntax_Syntax.binder_qual
                                                                = uu___14;
                                                              FStar_Syntax_Syntax.binder_positivity
                                                                = uu___15;
                                                              FStar_Syntax_Syntax.binder_attrs
                                                                = uu___16;_})
                                                             ->
                                                             let uu___17 =
                                                               let uu___18 =
                                                                 FStar_Syntax_Syntax.bv_to_name
                                                                   y in
                                                               (x, uu___18) in
                                                             FStar_Syntax_Syntax.NT
                                                               uu___17)
                                                    tbinders targs in
                                                FStar_Syntax_Subst.subst s
                                                  tbody in
                                              let env =
                                                FStar_Compiler_List.fold_left
                                                  (fun env1 ->
                                                     fun uu___9 ->
                                                       match uu___9 with
                                                       | {
                                                           FStar_Syntax_Syntax.binder_bv
                                                             = a;
                                                           FStar_Syntax_Syntax.binder_qual
                                                             = uu___10;
                                                           FStar_Syntax_Syntax.binder_positivity
                                                             = uu___11;
                                                           FStar_Syntax_Syntax.binder_attrs
                                                             = uu___12;_}
                                                           ->
                                                           FStar_Extraction_ML_UEnv.extend_ty
                                                             env1 a false) g
                                                  targs in
                                              let expected_t =
                                                term_as_mlty env
                                                  expected_source_ty in
                                              let polytype =
                                                let uu___9 =
                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                    targs
                                                    (FStar_Compiler_List.map
                                                       (fun uu___10 ->
                                                          match uu___10 with
                                                          | {
                                                              FStar_Syntax_Syntax.binder_bv
                                                                = x;
                                                              FStar_Syntax_Syntax.binder_qual
                                                                = uu___11;
                                                              FStar_Syntax_Syntax.binder_positivity
                                                                = uu___12;
                                                              FStar_Syntax_Syntax.binder_attrs
                                                                = uu___13;_}
                                                              ->
                                                              let uu___14 =
                                                                FStar_Extraction_ML_UEnv.lookup_ty
                                                                  env x in
                                                              uu___14.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                                (uu___9, expected_t) in
                                              let add_unit =
                                                match rest_args with
                                                | [] ->
                                                    (let uu___9 =
                                                       is_fstar_value body1 in
                                                     Prims.op_Negation uu___9)
                                                      ||
                                                      (let uu___9 =
                                                         FStar_Syntax_Util.is_pure_comp
                                                           c1 in
                                                       Prims.op_Negation
                                                         uu___9)
                                                | uu___9 -> false in
                                              let rest_args1 =
                                                if add_unit
                                                then
                                                  let uu___9 = unit_binder () in
                                                  uu___9 :: rest_args
                                                else rest_args in
                                              let polytype1 =
                                                if add_unit
                                                then
                                                  FStar_Extraction_ML_Syntax.push_unit
                                                    polytype
                                                else polytype in
                                              let body2 =
                                                FStar_Syntax_Util.abs
                                                  rest_args1 body1 copt in
                                              (lbname_, f_e,
                                                (lbtyp1, (targs, polytype1)),
                                                add_unit, body2))
                                       else
                                         failwith "Not enough type binders")
                              | FStar_Syntax_Syntax.Tm_uinst uu___7 ->
                                  let env =
                                    FStar_Compiler_List.fold_left
                                      (fun env1 ->
                                         fun uu___8 ->
                                           match uu___8 with
                                           | {
                                               FStar_Syntax_Syntax.binder_bv
                                                 = a;
                                               FStar_Syntax_Syntax.binder_qual
                                                 = uu___9;
                                               FStar_Syntax_Syntax.binder_positivity
                                                 = uu___10;
                                               FStar_Syntax_Syntax.binder_attrs
                                                 = uu___11;_}
                                               ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env1 a false) g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu___8 =
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        tbinders
                                        (FStar_Compiler_List.map
                                           (fun uu___9 ->
                                              match uu___9 with
                                              | {
                                                  FStar_Syntax_Syntax.binder_bv
                                                    = x;
                                                  FStar_Syntax_Syntax.binder_qual
                                                    = uu___10;
                                                  FStar_Syntax_Syntax.binder_positivity
                                                    = uu___11;
                                                  FStar_Syntax_Syntax.binder_attrs
                                                    = uu___12;_}
                                                  ->
                                                  let uu___13 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x in
                                                  uu___13.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                    (uu___8, expected_t) in
                                  let args =
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      tbinders
                                      (FStar_Compiler_List.map
                                         (fun uu___8 ->
                                            match uu___8 with
                                            | {
                                                FStar_Syntax_Syntax.binder_bv
                                                  = bv;
                                                FStar_Syntax_Syntax.binder_qual
                                                  = uu___9;
                                                FStar_Syntax_Syntax.binder_positivity
                                                  = uu___10;
                                                FStar_Syntax_Syntax.binder_attrs
                                                  = uu___11;_}
                                                ->
                                                let uu___12 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  uu___12
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         {
                                           FStar_Syntax_Syntax.hd = lbdef1;
                                           FStar_Syntax_Syntax.args = args
                                         }) lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_fvar uu___7 ->
                                  let env =
                                    FStar_Compiler_List.fold_left
                                      (fun env1 ->
                                         fun uu___8 ->
                                           match uu___8 with
                                           | {
                                               FStar_Syntax_Syntax.binder_bv
                                                 = a;
                                               FStar_Syntax_Syntax.binder_qual
                                                 = uu___9;
                                               FStar_Syntax_Syntax.binder_positivity
                                                 = uu___10;
                                               FStar_Syntax_Syntax.binder_attrs
                                                 = uu___11;_}
                                               ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env1 a false) g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu___8 =
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        tbinders
                                        (FStar_Compiler_List.map
                                           (fun uu___9 ->
                                              match uu___9 with
                                              | {
                                                  FStar_Syntax_Syntax.binder_bv
                                                    = x;
                                                  FStar_Syntax_Syntax.binder_qual
                                                    = uu___10;
                                                  FStar_Syntax_Syntax.binder_positivity
                                                    = uu___11;
                                                  FStar_Syntax_Syntax.binder_attrs
                                                    = uu___12;_}
                                                  ->
                                                  let uu___13 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x in
                                                  uu___13.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                    (uu___8, expected_t) in
                                  let args =
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      tbinders
                                      (FStar_Compiler_List.map
                                         (fun uu___8 ->
                                            match uu___8 with
                                            | {
                                                FStar_Syntax_Syntax.binder_bv
                                                  = bv;
                                                FStar_Syntax_Syntax.binder_qual
                                                  = uu___9;
                                                FStar_Syntax_Syntax.binder_positivity
                                                  = uu___10;
                                                FStar_Syntax_Syntax.binder_attrs
                                                  = uu___11;_}
                                                ->
                                                let uu___12 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  uu___12
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         {
                                           FStar_Syntax_Syntax.hd = lbdef1;
                                           FStar_Syntax_Syntax.args = args
                                         }) lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | FStar_Syntax_Syntax.Tm_name uu___7 ->
                                  let env =
                                    FStar_Compiler_List.fold_left
                                      (fun env1 ->
                                         fun uu___8 ->
                                           match uu___8 with
                                           | {
                                               FStar_Syntax_Syntax.binder_bv
                                                 = a;
                                               FStar_Syntax_Syntax.binder_qual
                                                 = uu___9;
                                               FStar_Syntax_Syntax.binder_positivity
                                                 = uu___10;
                                               FStar_Syntax_Syntax.binder_attrs
                                                 = uu___11;_}
                                               ->
                                               FStar_Extraction_ML_UEnv.extend_ty
                                                 env1 a false) g tbinders in
                                  let expected_t = term_as_mlty env tbody in
                                  let polytype =
                                    let uu___8 =
                                      FStar_Compiler_Effect.op_Bar_Greater
                                        tbinders
                                        (FStar_Compiler_List.map
                                           (fun uu___9 ->
                                              match uu___9 with
                                              | {
                                                  FStar_Syntax_Syntax.binder_bv
                                                    = x;
                                                  FStar_Syntax_Syntax.binder_qual
                                                    = uu___10;
                                                  FStar_Syntax_Syntax.binder_positivity
                                                    = uu___11;
                                                  FStar_Syntax_Syntax.binder_attrs
                                                    = uu___12;_}
                                                  ->
                                                  let uu___13 =
                                                    FStar_Extraction_ML_UEnv.lookup_ty
                                                      env x in
                                                  uu___13.FStar_Extraction_ML_UEnv.ty_b_name)) in
                                    (uu___8, expected_t) in
                                  let args =
                                    FStar_Compiler_Effect.op_Bar_Greater
                                      tbinders
                                      (FStar_Compiler_List.map
                                         (fun uu___8 ->
                                            match uu___8 with
                                            | {
                                                FStar_Syntax_Syntax.binder_bv
                                                  = bv;
                                                FStar_Syntax_Syntax.binder_qual
                                                  = uu___9;
                                                FStar_Syntax_Syntax.binder_positivity
                                                  = uu___10;
                                                FStar_Syntax_Syntax.binder_attrs
                                                  = uu___11;_}
                                                ->
                                                let uu___12 =
                                                  FStar_Syntax_Syntax.bv_to_name
                                                    bv in
                                                FStar_Compiler_Effect.op_Bar_Greater
                                                  uu___12
                                                  FStar_Syntax_Syntax.as_arg)) in
                                  let e =
                                    FStar_Syntax_Syntax.mk
                                      (FStar_Syntax_Syntax.Tm_app
                                         {
                                           FStar_Syntax_Syntax.hd = lbdef1;
                                           FStar_Syntax_Syntax.args = args
                                         }) lbdef1.FStar_Syntax_Syntax.pos in
                                  (lbname_, f_e,
                                    (lbtyp1, (tbinders, polytype)), false, e)
                              | uu___7 -> err_value_restriction lbdef1)))
               | uu___5 -> no_gen ()) in
      FStar_Compiler_Effect.op_Bar_Greater (FStar_Pervasives_Native.snd lbs)
        (FStar_Compiler_List.map maybe_generalize)
let (extract_lb_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.letbindings ->
      (FStar_Extraction_ML_UEnv.uenv * (FStar_Syntax_Syntax.fv *
        FStar_Extraction_ML_UEnv.exp_binding) Prims.list))
  =
  fun g ->
    fun lbs ->
      let is_top =
        FStar_Syntax_Syntax.is_top_level (FStar_Pervasives_Native.snd lbs) in
      let is_rec =
        (Prims.op_Negation is_top) && (FStar_Pervasives_Native.fst lbs) in
      let lbs1 = extract_lb_sig g lbs in
      FStar_Compiler_Util.fold_map
        (fun env ->
           fun uu___ ->
             match uu___ with
             | (lbname, e_tag, (typ, (binders, mltyscheme)), add_unit, _body)
                 ->
                 let uu___1 =
                   FStar_Extraction_ML_UEnv.extend_lb env lbname typ
                     mltyscheme add_unit in
                 (match uu___1 with
                  | (env1, uu___2, exp_binding) ->
                      let uu___3 =
                        let uu___4 = FStar_Compiler_Util.right lbname in
                        (uu___4, exp_binding) in
                      (env1, uu___3))) g lbs1
let rec (check_term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      FStar_Extraction_ML_Syntax.e_tag ->
        FStar_Extraction_ML_Syntax.mlty ->
          (FStar_Extraction_ML_Syntax.mlexpr *
            FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun e ->
      fun f ->
        fun ty ->
          FStar_Extraction_ML_UEnv.debug g
            (fun uu___1 ->
               let uu___2 = FStar_Syntax_Print.term_to_string e in
               let uu___3 =
                 let uu___4 =
                   FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                 FStar_Extraction_ML_Code.string_of_mlty uu___4 ty in
               let uu___4 = FStar_Extraction_ML_Util.eff_to_string f in
               FStar_Compiler_Util.print3
                 "Checking %s at type %s and eff %s\n" uu___2 uu___3 uu___4);
          (match (f, ty) with
           | (FStar_Extraction_ML_Syntax.E_ERASABLE, uu___1) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | (FStar_Extraction_ML_Syntax.E_PURE,
              FStar_Extraction_ML_Syntax.MLTY_Erased) ->
               (FStar_Extraction_ML_Syntax.ml_unit,
                 FStar_Extraction_ML_Syntax.MLTY_Erased)
           | uu___1 ->
               let uu___2 = term_as_mlexpr g e in
               (match uu___2 with
                | (ml_e, tag, t) ->
                    let uu___3 = FStar_Extraction_ML_Util.eff_leq tag f in
                    if uu___3
                    then
                      let uu___4 =
                        maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t ty in
                      (uu___4, ty)
                    else
                      (match (tag, f, ty) with
                       | (FStar_Extraction_ML_Syntax.E_ERASABLE,
                          FStar_Extraction_ML_Syntax.E_PURE,
                          FStar_Extraction_ML_Syntax.MLTY_Erased) ->
                           let uu___5 =
                             maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e t
                               ty in
                           (uu___5, ty)
                       | uu___5 ->
                           (err_unexpected_eff g e ty f tag;
                            (let uu___7 =
                               maybe_coerce e.FStar_Syntax_Syntax.pos g ml_e
                                 t ty in
                             (uu___7, ty))))))
and (term_as_mlexpr :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun e ->
      let uu___ = term_as_mlexpr' g e in
      match uu___ with
      | (e1, f, t) ->
          let uu___1 = maybe_promote_effect e1 f t in
          (match uu___1 with | (e2, f1) -> (e2, f1, t))
and (term_as_mlexpr' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.term ->
      (FStar_Extraction_ML_Syntax.mlexpr * FStar_Extraction_ML_Syntax.e_tag *
        FStar_Extraction_ML_Syntax.mlty))
  =
  fun g ->
    fun top ->
      let top1 = FStar_Syntax_Subst.compress top in
      FStar_Extraction_ML_UEnv.debug g
        (fun u ->
           let uu___1 =
             let uu___2 =
               FStar_Compiler_Range_Ops.string_of_range
                 top1.FStar_Syntax_Syntax.pos in
             let uu___3 = FStar_Syntax_Print.tag_of_term top1 in
             let uu___4 = FStar_Syntax_Print.term_to_string top1 in
             FStar_Compiler_Util.format3 "%s: term_as_mlexpr' (%s) :  %s \n"
               uu___2 uu___3 uu___4 in
           FStar_Compiler_Util.print_string uu___1);
      (let is_match t =
         let uu___1 =
           let uu___2 =
             let uu___3 =
               FStar_Compiler_Effect.op_Bar_Greater t
                 FStar_Syntax_Subst.compress in
             FStar_Compiler_Effect.op_Bar_Greater uu___3
               FStar_Syntax_Util.unascribe in
           uu___2.FStar_Syntax_Syntax.n in
         match uu___1 with
         | FStar_Syntax_Syntax.Tm_match uu___2 -> true
         | uu___2 -> false in
       let should_apply_to_match_branches =
         FStar_Compiler_List.for_all
           (fun uu___1 ->
              match uu___1 with
              | (t, uu___2) ->
                  let uu___3 =
                    let uu___4 =
                      FStar_Compiler_Effect.op_Bar_Greater t
                        FStar_Syntax_Subst.compress in
                    uu___4.FStar_Syntax_Syntax.n in
                  (match uu___3 with
                   | FStar_Syntax_Syntax.Tm_name uu___4 -> true
                   | FStar_Syntax_Syntax.Tm_fvar uu___4 -> true
                   | FStar_Syntax_Syntax.Tm_constant uu___4 -> true
                   | uu___4 -> false)) in
       let apply_to_match_branches head args =
         let uu___1 =
           let uu___2 =
             let uu___3 =
               FStar_Compiler_Effect.op_Bar_Greater head
                 FStar_Syntax_Subst.compress in
             FStar_Compiler_Effect.op_Bar_Greater uu___3
               FStar_Syntax_Util.unascribe in
           uu___2.FStar_Syntax_Syntax.n in
         match uu___1 with
         | FStar_Syntax_Syntax.Tm_match
             { FStar_Syntax_Syntax.scrutinee = scrutinee;
               FStar_Syntax_Syntax.ret_opt = uu___2;
               FStar_Syntax_Syntax.brs = branches;
               FStar_Syntax_Syntax.rc_opt1 = uu___3;_}
             ->
             let branches1 =
               FStar_Compiler_Effect.op_Bar_Greater branches
                 (FStar_Compiler_List.map
                    (fun uu___4 ->
                       match uu___4 with
                       | (pat, when_opt, body) ->
                           (pat, when_opt,
                             {
                               FStar_Syntax_Syntax.n =
                                 (FStar_Syntax_Syntax.Tm_app
                                    {
                                      FStar_Syntax_Syntax.hd = body;
                                      FStar_Syntax_Syntax.args = args
                                    });
                               FStar_Syntax_Syntax.pos =
                                 (body.FStar_Syntax_Syntax.pos);
                               FStar_Syntax_Syntax.vars =
                                 (body.FStar_Syntax_Syntax.vars);
                               FStar_Syntax_Syntax.hash_code =
                                 (body.FStar_Syntax_Syntax.hash_code)
                             }))) in
             {
               FStar_Syntax_Syntax.n =
                 (FStar_Syntax_Syntax.Tm_match
                    {
                      FStar_Syntax_Syntax.scrutinee = scrutinee;
                      FStar_Syntax_Syntax.ret_opt =
                        FStar_Pervasives_Native.None;
                      FStar_Syntax_Syntax.brs = branches1;
                      FStar_Syntax_Syntax.rc_opt1 =
                        FStar_Pervasives_Native.None
                    });
               FStar_Syntax_Syntax.pos = (head.FStar_Syntax_Syntax.pos);
               FStar_Syntax_Syntax.vars = (head.FStar_Syntax_Syntax.vars);
               FStar_Syntax_Syntax.hash_code =
                 (head.FStar_Syntax_Syntax.hash_code)
             }
         | uu___2 ->
             failwith
               "Impossible! cannot apply args to match branches if head is not a match" in
       let t = FStar_Syntax_Subst.compress top1 in
       match t.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_unknown ->
           let uu___1 =
             let uu___2 = FStar_Syntax_Print.tag_of_term t in
             FStar_Compiler_Util.format1 "Impossible: Unexpected term: %s"
               uu___2 in
           failwith uu___1
       | FStar_Syntax_Syntax.Tm_delayed uu___1 ->
           let uu___2 =
             let uu___3 = FStar_Syntax_Print.tag_of_term t in
             FStar_Compiler_Util.format1 "Impossible: Unexpected term: %s"
               uu___3 in
           failwith uu___2
       | FStar_Syntax_Syntax.Tm_uvar uu___1 ->
           let uu___2 =
             let uu___3 = FStar_Syntax_Print.tag_of_term t in
             FStar_Compiler_Util.format1 "Impossible: Unexpected term: %s"
               uu___3 in
           failwith uu___2
       | FStar_Syntax_Syntax.Tm_bvar uu___1 ->
           let uu___2 =
             let uu___3 = FStar_Syntax_Print.tag_of_term t in
             FStar_Compiler_Util.format1 "Impossible: Unexpected term: %s"
               uu___3 in
           failwith uu___2
       | FStar_Syntax_Syntax.Tm_lazy i ->
           let uu___1 = FStar_Syntax_Util.unfold_lazy i in
           term_as_mlexpr g uu___1
       | FStar_Syntax_Syntax.Tm_type uu___1 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_refine uu___1 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_arrow uu___1 ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_dynamic;
              FStar_Syntax_Syntax.antiquotations = uu___1;_})
           ->
           let uu___2 =
             let uu___3 =
               let uu___4 = FStar_Parser_Const.failwith_lid () in
               FStar_Syntax_Syntax.lid_as_fv uu___4
                 FStar_Pervasives_Native.None in
             FStar_Extraction_ML_UEnv.lookup_fv t.FStar_Syntax_Syntax.pos g
               uu___3 in
           (match uu___2 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu___3;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu___4;_} ->
                let uu___5 =
                  let uu___6 =
                    let uu___7 =
                      let uu___8 =
                        let uu___9 =
                          FStar_Compiler_Effect.op_Less_Bar
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Cannot evaluate open quotation at runtime")) in
                        [uu___9] in
                      (fw, uu___8) in
                    FStar_Extraction_ML_Syntax.MLE_App uu___7 in
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu___6 in
                (uu___5, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_quoted
           (qt,
            { FStar_Syntax_Syntax.qkind = FStar_Syntax_Syntax.Quote_static;
              FStar_Syntax_Syntax.antiquotations = (shift, aqs);_})
           ->
           let uu___1 = FStar_Reflection_V2_Builtins.inspect_ln qt in
           (match uu___1 with
            | FStar_Reflection_V2_Data.Tv_BVar bv ->
                if bv.FStar_Syntax_Syntax.index < shift
                then
                  let tv' = FStar_Reflection_V2_Data.Tv_BVar bv in
                  let tv =
                    let uu___2 =
                      FStar_Syntax_Embeddings_Base.embed
                        FStar_Reflection_V2_Embeddings.e_term_view tv' in
                    uu___2 t.FStar_Syntax_Syntax.pos
                      FStar_Pervasives_Native.None
                      FStar_Syntax_Embeddings_Base.id_norm_cb in
                  let t1 =
                    let uu___2 =
                      let uu___3 = FStar_Syntax_Syntax.as_arg tv in [uu___3] in
                    FStar_Syntax_Util.mk_app
                      (FStar_Reflection_V2_Constants.refl_constant_term
                         FStar_Reflection_V2_Constants.fstar_refl_pack_ln)
                      uu___2 in
                  term_as_mlexpr g t1
                else
                  (let tm = FStar_Syntax_Syntax.lookup_aq bv (shift, aqs) in
                   term_as_mlexpr g tm)
            | tv ->
                let tv1 =
                  let uu___2 =
                    let uu___3 =
                      FStar_Reflection_V2_Embeddings.e_term_view_aq
                        (shift, aqs) in
                    FStar_Syntax_Embeddings_Base.embed uu___3 tv in
                  uu___2 t.FStar_Syntax_Syntax.pos
                    FStar_Pervasives_Native.None
                    FStar_Syntax_Embeddings_Base.id_norm_cb in
                let t1 =
                  let uu___2 =
                    let uu___3 = FStar_Syntax_Syntax.as_arg tv1 in [uu___3] in
                  FStar_Syntax_Util.mk_app
                    (FStar_Reflection_V2_Constants.refl_constant_term
                       FStar_Reflection_V2_Constants.fstar_refl_pack_ln)
                    uu___2 in
                term_as_mlexpr g t1)
       | FStar_Syntax_Syntax.Tm_meta
           { FStar_Syntax_Syntax.tm2 = t1;
             FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_monadic
               (m, uu___1);_}
           ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           (match t2.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_let
                { FStar_Syntax_Syntax.lbs = (false, lb::[]);
                  FStar_Syntax_Syntax.body1 = body;_}
                when
                FStar_Compiler_Util.is_left lb.FStar_Syntax_Syntax.lbname ->
                let tcenv = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                let uu___2 =
                  let uu___3 = FStar_TypeChecker_Env.effect_decl_opt tcenv m in
                  FStar_Compiler_Util.must uu___3 in
                (match uu___2 with
                 | (ed, qualifiers) ->
                     let uu___3 =
                       let uu___4 =
                         FStar_TypeChecker_Util.effect_extraction_mode tcenv
                           ed.FStar_Syntax_Syntax.mname in
                       uu___4 = FStar_Syntax_Syntax.Extract_primitive in
                     if uu___3
                     then term_as_mlexpr g t2
                     else
                       (let uu___5 =
                          let uu___6 =
                            FStar_Ident.string_of_lid
                              ed.FStar_Syntax_Syntax.mname in
                          FStar_Compiler_Util.format1
                            "This should not happen (should have been handled at Tm_abs level for effect %s)"
                            uu___6 in
                        failwith uu___5))
            | uu___2 -> term_as_mlexpr g t2)
       | FStar_Syntax_Syntax.Tm_meta
           { FStar_Syntax_Syntax.tm2 = t1;
             FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_monadic_lift
               (m1, _m2, _ty);_}
           when
           let uu___1 = effect_as_etag g m1 in
           uu___1 = FStar_Extraction_ML_Syntax.E_ERASABLE ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_ERASABLE,
             FStar_Extraction_ML_Syntax.MLTY_Erased)
       | FStar_Syntax_Syntax.Tm_meta
           { FStar_Syntax_Syntax.tm2 = t1;
             FStar_Syntax_Syntax.meta = FStar_Syntax_Syntax.Meta_desugared
               (FStar_Syntax_Syntax.Machine_integer (signedness, width));_}
           ->
           let t2 = FStar_Syntax_Subst.compress t1 in
           let t3 = FStar_Syntax_Util.unascribe t2 in
           (match t3.FStar_Syntax_Syntax.n with
            | FStar_Syntax_Syntax.Tm_app
                { FStar_Syntax_Syntax.hd = hd;
                  FStar_Syntax_Syntax.args = (x, uu___1)::[];_}
                ->
                let x1 = FStar_Syntax_Subst.compress x in
                let x2 = FStar_Syntax_Util.unascribe x1 in
                (match x2.FStar_Syntax_Syntax.n with
                 | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
                     (repr, uu___2)) ->
                     let uu___3 =
                       let uu___4 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                       FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term
                         uu___4 t3 true in
                     (match uu___3 with
                      | (uu___4, ty, uu___5) ->
                          let ml_ty = term_as_mlty g ty in
                          let ml_const =
                            FStar_Const.Const_int
                              (repr,
                                (FStar_Pervasives_Native.Some
                                   (signedness, width))) in
                          let uu___6 =
                            let uu___7 =
                              FStar_Extraction_ML_Util.mlexpr_of_const
                                t3.FStar_Syntax_Syntax.pos ml_const in
                            FStar_Extraction_ML_Syntax.with_ty ml_ty uu___7 in
                          (uu___6, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
                 | uu___2 -> term_as_mlexpr g t3)
            | uu___1 -> term_as_mlexpr g t3)
       | FStar_Syntax_Syntax.Tm_meta
           { FStar_Syntax_Syntax.tm2 = t1;
             FStar_Syntax_Syntax.meta = uu___1;_}
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_uinst (t1, uu___1) -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu___1 =
             let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
             FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term uu___2 t true in
           (match uu___1 with
            | (uu___2, ty, uu___3) ->
                let ml_ty = term_as_mlty g ty in
                let uu___4 =
                  let uu___5 =
                    FStar_Extraction_ML_Util.mlexpr_of_const
                      t.FStar_Syntax_Syntax.pos c in
                  FStar_Extraction_ML_Syntax.with_ty ml_ty uu___5 in
                (uu___4, FStar_Extraction_ML_Syntax.E_PURE, ml_ty))
       | FStar_Syntax_Syntax.Tm_name uu___1 ->
           let uu___2 = is_type g t in
           if uu___2
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu___4 = FStar_Extraction_ML_UEnv.lookup_term g t in
              match uu___4 with
              | (FStar_Pervasives.Inl uu___5, uu___6) ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
              | (FStar_Pervasives.Inr
                 { FStar_Extraction_ML_UEnv.exp_b_name = uu___5;
                   FStar_Extraction_ML_UEnv.exp_b_expr = x;
                   FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_},
                 qual) ->
                  (match mltys with
                   | ([], t1) when t1 = FStar_Extraction_ML_Syntax.ml_unit_ty
                       ->
                       (FStar_Extraction_ML_Syntax.ml_unit,
                         FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | ([], t1) ->
                       let uu___6 =
                         maybe_eta_data_and_project_record g qual t1 x in
                       (uu___6, FStar_Extraction_ML_Syntax.E_PURE, t1)
                   | uu___6 -> instantiate_maybe_partial g x mltys []))
       | FStar_Syntax_Syntax.Tm_fvar fv ->
           let uu___1 = is_type g t in
           if uu___1
           then
             (FStar_Extraction_ML_Syntax.ml_unit,
               FStar_Extraction_ML_Syntax.E_PURE,
               FStar_Extraction_ML_Syntax.ml_unit_ty)
           else
             (let uu___3 =
                FStar_Extraction_ML_UEnv.try_lookup_fv
                  t.FStar_Syntax_Syntax.pos g fv in
              match uu___3 with
              | FStar_Pervasives_Native.None ->
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.MLTY_Erased)
              | FStar_Pervasives_Native.Some
                  { FStar_Extraction_ML_UEnv.exp_b_name = uu___4;
                    FStar_Extraction_ML_UEnv.exp_b_expr = x;
                    FStar_Extraction_ML_UEnv.exp_b_tscheme = mltys;_}
                  ->
                  (FStar_Extraction_ML_UEnv.debug g
                     (fun uu___6 ->
                        let uu___7 = FStar_Syntax_Print.fv_to_string fv in
                        let uu___8 =
                          let uu___9 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                          FStar_Extraction_ML_Code.string_of_mlexpr uu___9 x in
                        let uu___9 =
                          let uu___10 =
                            FStar_Extraction_ML_UEnv.current_module_of_uenv g in
                          FStar_Extraction_ML_Code.string_of_mlty uu___10
                            (FStar_Pervasives_Native.snd mltys) in
                        FStar_Compiler_Util.print3
                          "looked up %s: got %s at %s \n" uu___7 uu___8
                          uu___9);
                   (match mltys with
                    | ([], t1) when
                        t1 = FStar_Extraction_ML_Syntax.ml_unit_ty ->
                        (FStar_Extraction_ML_Syntax.ml_unit,
                          FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | ([], t1) ->
                        let uu___6 =
                          maybe_eta_data_and_project_record g
                            fv.FStar_Syntax_Syntax.fv_qual t1 x in
                        (uu___6, FStar_Extraction_ML_Syntax.E_PURE, t1)
                    | uu___6 -> instantiate_maybe_partial g x mltys [])))
       | FStar_Syntax_Syntax.Tm_abs
           { FStar_Syntax_Syntax.bs = bs; FStar_Syntax_Syntax.body = body;
             FStar_Syntax_Syntax.rc_opt = rcopt;_}
           ->
           let uu___1 = FStar_Syntax_Subst.open_term bs body in
           (match uu___1 with
            | (bs1, body1) ->
                let uu___2 = binders_as_ml_binders g bs1 in
                (match uu___2 with
                 | (ml_bs, env) ->
                     let body2 =
                       match rcopt with
                       | FStar_Pervasives_Native.Some rc ->
                           let uu___3 =
                             FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
                           maybe_reify_term uu___3 body1
                             rc.FStar_Syntax_Syntax.residual_effect
                       | FStar_Pervasives_Native.None ->
                           (FStar_Extraction_ML_UEnv.debug g
                              (fun uu___4 ->
                                 let uu___5 =
                                   FStar_Syntax_Print.term_to_string body1 in
                                 FStar_Compiler_Util.print1
                                   "No computation type for: %s\n" uu___5);
                            body1) in
                     let uu___3 = term_as_mlexpr env body2 in
                     (match uu___3 with
                      | (ml_body, f, t1) ->
                          let uu___4 =
                            FStar_Compiler_List.fold_right
                              (fun uu___5 ->
                                 fun uu___6 ->
                                   match (uu___5, uu___6) with
                                   | ((uu___7, targ), (f1, t2)) ->
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         (FStar_Extraction_ML_Syntax.MLTY_Fun
                                            (targ, f1, t2)))) ml_bs (f, t1) in
                          (match uu___4 with
                           | (f1, tfun) ->
                               let uu___5 =
                                 FStar_Compiler_Effect.op_Less_Bar
                                   (FStar_Extraction_ML_Syntax.with_ty tfun)
                                   (FStar_Extraction_ML_Syntax.MLE_Fun
                                      (ml_bs, ml_body)) in
                               (uu___5, f1, tfun)))))
       | FStar_Syntax_Syntax.Tm_app
           {
             FStar_Syntax_Syntax.hd =
               {
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_range_of);
                 FStar_Syntax_Syntax.pos = uu___1;
                 FStar_Syntax_Syntax.vars = uu___2;
                 FStar_Syntax_Syntax.hash_code = uu___3;_};
             FStar_Syntax_Syntax.args = (a1, uu___4)::[];_}
           ->
           let ty =
             let uu___5 =
               FStar_Syntax_Syntax.tabbrev FStar_Parser_Const.range_lid in
             term_as_mlty g uu___5 in
           let uu___5 =
             let uu___6 =
               FStar_Extraction_ML_Util.mlexpr_of_range
                 a1.FStar_Syntax_Syntax.pos in
             FStar_Compiler_Effect.op_Less_Bar
               (FStar_Extraction_ML_Syntax.with_ty ty) uu___6 in
           (uu___5, FStar_Extraction_ML_Syntax.E_PURE, ty)
       | FStar_Syntax_Syntax.Tm_app
           {
             FStar_Syntax_Syntax.hd =
               {
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_set_range_of);
                 FStar_Syntax_Syntax.pos = uu___1;
                 FStar_Syntax_Syntax.vars = uu___2;
                 FStar_Syntax_Syntax.hash_code = uu___3;_};
             FStar_Syntax_Syntax.args = (t1, uu___4)::(r, uu___5)::[];_}
           -> term_as_mlexpr g t1
       | FStar_Syntax_Syntax.Tm_app
           {
             FStar_Syntax_Syntax.hd =
               {
                 FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                   (FStar_Const.Const_reflect uu___1);
                 FStar_Syntax_Syntax.pos = uu___2;
                 FStar_Syntax_Syntax.vars = uu___3;
                 FStar_Syntax_Syntax.hash_code = uu___4;_};
             FStar_Syntax_Syntax.args = uu___5;_}
           ->
           let uu___6 =
             let uu___7 =
               let uu___8 = FStar_Parser_Const.failwith_lid () in
               FStar_Syntax_Syntax.lid_as_fv uu___8
                 FStar_Pervasives_Native.None in
             FStar_Extraction_ML_UEnv.lookup_fv t.FStar_Syntax_Syntax.pos g
               uu___7 in
           (match uu___6 with
            | { FStar_Extraction_ML_UEnv.exp_b_name = uu___7;
                FStar_Extraction_ML_UEnv.exp_b_expr = fw;
                FStar_Extraction_ML_UEnv.exp_b_tscheme = uu___8;_} ->
                let uu___9 =
                  let uu___10 =
                    let uu___11 =
                      let uu___12 =
                        let uu___13 =
                          FStar_Compiler_Effect.op_Less_Bar
                            (FStar_Extraction_ML_Syntax.with_ty
                               FStar_Extraction_ML_Syntax.ml_string_ty)
                            (FStar_Extraction_ML_Syntax.MLE_Const
                               (FStar_Extraction_ML_Syntax.MLC_String
                                  "Extraction of reflect is not supported")) in
                        [uu___13] in
                      (fw, uu___12) in
                    FStar_Extraction_ML_Syntax.MLE_App uu___11 in
                  FStar_Compiler_Effect.op_Less_Bar
                    (FStar_Extraction_ML_Syntax.with_ty
                       FStar_Extraction_ML_Syntax.ml_int_ty) uu___10 in
                (uu___9, FStar_Extraction_ML_Syntax.E_PURE,
                  FStar_Extraction_ML_Syntax.ml_int_ty))
       | FStar_Syntax_Syntax.Tm_app uu___1 when is_steel_with_invariant_g t
           ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.MLTY_Erased)
       | FStar_Syntax_Syntax.Tm_app uu___1 when
           let uu___2 = is_steel_with_invariant t in
           FStar_Pervasives_Native.uu___is_Some uu___2 ->
           let body =
             let uu___2 = is_steel_with_invariant t in
             FStar_Pervasives_Native.__proj__Some__item__v uu___2 in
           let tm =
             let uu___2 =
               let uu___3 =
                 FStar_Syntax_Syntax.as_arg FStar_Syntax_Syntax.unit_const in
               [uu___3] in
             FStar_Syntax_Syntax.mk_Tm_app body uu___2
               body.FStar_Syntax_Syntax.pos in
           term_as_mlexpr g tm
       | FStar_Syntax_Syntax.Tm_app uu___1 when is_steel_new_invariant t ->
           (FStar_Extraction_ML_Syntax.ml_unit,
             FStar_Extraction_ML_Syntax.E_PURE,
             FStar_Extraction_ML_Syntax.ml_unit_ty)
       | FStar_Syntax_Syntax.Tm_app
           { FStar_Syntax_Syntax.hd = head;
             FStar_Syntax_Syntax.args = args;_}
           when
           (is_match head) &&
             (FStar_Compiler_Effect.op_Bar_Greater args
                should_apply_to_match_branches)
           ->
           let uu___1 =
             FStar_Compiler_Effect.op_Bar_Greater args
               (apply_to_match_branches head) in
           FStar_Compiler_Effect.op_Bar_Greater uu___1 (term_as_mlexpr g)
       | FStar_Syntax_Syntax.Tm_app
           { FStar_Syntax_Syntax.hd = head;
             FStar_Syntax_Syntax.args = args;_}
           ->
           let is_total rc =
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_Tot_lid)
               ||
               (FStar_Compiler_Effect.op_Bar_Greater
                  rc.FStar_Syntax_Syntax.residual_flags
                  (FStar_Compiler_List.existsb
                     (fun uu___1 ->
                        match uu___1 with
                        | FStar_Syntax_Syntax.TOTAL -> true
                        | uu___2 -> false))) in
           let uu___1 =
             let uu___2 =
               let uu___3 =
                 FStar_Compiler_Effect.op_Bar_Greater head
                   FStar_Syntax_Subst.compress in
               FStar_Compiler_Effect.op_Bar_Greater uu___3
                 FStar_Syntax_Util.unascribe in
             uu___2.FStar_Syntax_Syntax.n in
           (match uu___1 with
            | FStar_Syntax_Syntax.Tm_abs
                { FStar_Syntax_Syntax.bs = bs;
                  FStar_Syntax_Syntax.body = uu___2;
                  FStar_Syntax_Syntax.rc_opt = rc;_}
                ->
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Normalize.normalize
                      [FStar_TypeChecker_Env.Beta;
                      FStar_TypeChecker_Env.Iota;
                      FStar_TypeChecker_Env.Zeta;
                      FStar_TypeChecker_Env.EraseUniverses;
                      FStar_TypeChecker_Env.AllowUnboundUniverses;
                      FStar_TypeChecker_Env.ForExtraction] uu___5 in
                  FStar_Compiler_Effect.op_Bar_Greater t uu___4 in
                FStar_Compiler_Effect.op_Bar_Greater uu___3
                  (term_as_mlexpr g)
            | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify lopt)
                ->
                (match lopt with
                 | FStar_Pervasives_Native.Some l ->
                     let e =
                       let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                       let uu___3 =
                         let uu___4 =
                           FStar_Compiler_Effect.op_Bar_Greater args
                             FStar_Compiler_List.hd in
                         FStar_Compiler_Effect.op_Bar_Greater uu___4
                           FStar_Pervasives_Native.fst in
                       maybe_reify_term uu___2 uu___3 l in
                     let tm =
                       let uu___2 = FStar_TypeChecker_Util.remove_reify e in
                       let uu___3 = FStar_Compiler_List.tl args in
                       FStar_Syntax_Syntax.mk_Tm_app uu___2 uu___3
                         t.FStar_Syntax_Syntax.pos in
                     term_as_mlexpr g tm
                 | FStar_Pervasives_Native.None ->
                     let uu___2 =
                       let uu___3 =
                         let uu___4 = FStar_Syntax_Print.term_to_string top1 in
                         FStar_Compiler_Util.format1
                           "Cannot extract %s (reify effect is not set)"
                           uu___4 in
                       (FStar_Errors_Codes.Fatal_ExtractionUnsupported,
                         uu___3) in
                     FStar_Errors.raise_error uu___2
                       top1.FStar_Syntax_Syntax.pos)
            | uu___2 ->
                let rec extract_app is_data uu___3 uu___4 restArgs =
                  match (uu___3, uu___4) with
                  | ((mlhead, mlargs_f), (f, t1)) ->
                      let mk_head uu___5 =
                        let mlargs =
                          FStar_Compiler_Effect.op_Bar_Greater
                            (FStar_Compiler_List.rev mlargs_f)
                            (FStar_Compiler_List.map
                               FStar_Pervasives_Native.fst) in
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_Extraction_ML_Syntax.with_ty t1)
                          (FStar_Extraction_ML_Syntax.MLE_App
                             (mlhead, mlargs)) in
                      (FStar_Extraction_ML_UEnv.debug g
                         (fun uu___6 ->
                            let uu___7 =
                              let uu___8 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              let uu___9 = mk_head () in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu___8 uu___9 in
                            let uu___8 =
                              let uu___9 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              FStar_Extraction_ML_Code.string_of_mlty uu___9
                                t1 in
                            let uu___9 =
                              match restArgs with
                              | [] -> "none"
                              | (hd, uu___10)::uu___11 ->
                                  FStar_Syntax_Print.term_to_string hd in
                            FStar_Compiler_Util.print3
                              "extract_app ml_head=%s type of head = %s, next arg = %s\n"
                              uu___7 uu___8 uu___9);
                       (match (restArgs, t1) with
                        | ([], uu___6) ->
                            let app =
                              let uu___7 = mk_head () in
                              maybe_eta_data_and_project_record g is_data t1
                                uu___7 in
                            (app, f, t1)
                        | ((arg, uu___6)::rest,
                           FStar_Extraction_ML_Syntax.MLTY_Fun
                           (formal_t, f', t2)) when
                            (is_type g arg) &&
                              (type_leq g formal_t
                                 FStar_Extraction_ML_Syntax.ml_unit_ty)
                            ->
                            let uu___7 =
                              let uu___8 =
                                FStar_Extraction_ML_Util.join
                                  arg.FStar_Syntax_Syntax.pos f f' in
                              (uu___8, t2) in
                            extract_app is_data
                              (mlhead,
                                ((FStar_Extraction_ML_Syntax.ml_unit,
                                   FStar_Extraction_ML_Syntax.E_PURE) ::
                                mlargs_f)) uu___7 rest
                        | ((e0, uu___6)::rest,
                           FStar_Extraction_ML_Syntax.MLTY_Fun
                           (tExpected, f', t2)) ->
                            let r = e0.FStar_Syntax_Syntax.pos in
                            let expected_effect =
                              let uu___7 =
                                (FStar_Options.lax ()) &&
                                  (FStar_TypeChecker_Util.short_circuit_head
                                     head) in
                              if uu___7
                              then FStar_Extraction_ML_Syntax.E_IMPURE
                              else FStar_Extraction_ML_Syntax.E_PURE in
                            let uu___7 =
                              check_term_as_mlexpr g e0 expected_effect
                                tExpected in
                            (match uu___7 with
                             | (e01, tInferred) ->
                                 let uu___8 =
                                   let uu___9 =
                                     FStar_Extraction_ML_Util.join_l r
                                       [f; f'] in
                                   (uu___9, t2) in
                                 extract_app is_data
                                   (mlhead, ((e01, expected_effect) ::
                                     mlargs_f)) uu___8 rest)
                        | uu___6 ->
                            let uu___7 =
                              FStar_Extraction_ML_Util.udelta_unfold g t1 in
                            (match uu___7 with
                             | FStar_Pervasives_Native.Some t2 ->
                                 extract_app is_data (mlhead, mlargs_f)
                                   (f, t2) restArgs
                             | FStar_Pervasives_Native.None ->
                                 (match t1 with
                                  | FStar_Extraction_ML_Syntax.MLTY_Erased ->
                                      (FStar_Extraction_ML_Syntax.ml_unit,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        t1)
                                  | FStar_Extraction_ML_Syntax.MLTY_Top ->
                                      let t2 =
                                        FStar_Compiler_List.fold_right
                                          (fun t3 ->
                                             fun out ->
                                               FStar_Extraction_ML_Syntax.MLTY_Fun
                                                 (FStar_Extraction_ML_Syntax.MLTY_Top,
                                                   FStar_Extraction_ML_Syntax.E_PURE,
                                                   out)) restArgs
                                          FStar_Extraction_ML_Syntax.MLTY_Top in
                                      let mlhead1 =
                                        let mlargs =
                                          FStar_Compiler_Effect.op_Bar_Greater
                                            (FStar_Compiler_List.rev mlargs_f)
                                            (FStar_Compiler_List.map
                                               FStar_Pervasives_Native.fst) in
                                        let head1 =
                                          FStar_Compiler_Effect.op_Less_Bar
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs)) in
                                        maybe_coerce
                                          top1.FStar_Syntax_Syntax.pos g
                                          head1
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t2 in
                                      extract_app is_data (mlhead1, [])
                                        (f, t2) restArgs
                                  | uu___8 ->
                                      let mlhead1 =
                                        let mlargs =
                                          FStar_Compiler_Effect.op_Bar_Greater
                                            (FStar_Compiler_List.rev mlargs_f)
                                            (FStar_Compiler_List.map
                                               FStar_Pervasives_Native.fst) in
                                        let head1 =
                                          FStar_Compiler_Effect.op_Less_Bar
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.MLTY_Top)
                                            (FStar_Extraction_ML_Syntax.MLE_App
                                               (mlhead, mlargs)) in
                                        maybe_coerce
                                          top1.FStar_Syntax_Syntax.pos g
                                          head1
                                          FStar_Extraction_ML_Syntax.MLTY_Top
                                          t1 in
                                      err_ill_typed_application g top1
                                        mlhead1 restArgs t1)))) in
                let extract_app_maybe_projector is_data mlhead uu___3 args1 =
                  match uu___3 with
                  | (f, t1) ->
                      (match is_data with
                       | FStar_Pervasives_Native.Some
                           (FStar_Syntax_Syntax.Record_projector uu___4) ->
                           let rec remove_implicits args2 f1 t2 =
                             match (args2, t2) with
                             | ((a0, FStar_Pervasives_Native.Some
                                 { FStar_Syntax_Syntax.aqual_implicit = true;
                                   FStar_Syntax_Syntax.aqual_attributes =
                                     uu___5;_})::args3,
                                FStar_Extraction_ML_Syntax.MLTY_Fun
                                (uu___6, f', t3)) ->
                                 let uu___7 =
                                   FStar_Extraction_ML_Util.join
                                     a0.FStar_Syntax_Syntax.pos f1 f' in
                                 remove_implicits args3 uu___7 t3
                             | uu___5 -> (args2, f1, t2) in
                           let uu___5 = remove_implicits args1 f t1 in
                           (match uu___5 with
                            | (args2, f1, t2) ->
                                extract_app is_data (mlhead, []) (f1, t2)
                                  args2)
                       | uu___4 ->
                           extract_app is_data (mlhead, []) (f, t1) args1) in
                let extract_app_with_instantiations uu___3 =
                  let head1 = FStar_Syntax_Util.un_uinst head in
                  match head1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Tm_name uu___4 ->
                      let uu___5 =
                        let uu___6 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1 in
                        match uu___6 with
                        | (FStar_Pervasives.Inr exp_b, q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu___8 ->
                                  let uu___9 =
                                    FStar_Syntax_Print.term_to_string head1 in
                                  let uu___10 =
                                    let uu___11 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu___11
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr in
                                  let uu___11 =
                                    let uu___12 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu___12
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme) in
                                  FStar_Compiler_Util.print3
                                    "@@@looked up %s: got %s at %s\n" uu___9
                                    uu___10 uu___11);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu___7 -> failwith "FIXME Ty" in
                      (match uu___5 with
                       | ((head_ml, (vars, t1)), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu___6)::uu___7 -> is_type g a
                             | uu___6 -> false in
                           let uu___6 =
                             let n = FStar_Compiler_List.length vars in
                             let uu___7 =
                               if (FStar_Compiler_List.length args) <= n
                               then
                                 let uu___8 =
                                   FStar_Compiler_List.map
                                     (fun uu___9 ->
                                        match uu___9 with
                                        | (x, uu___10) -> term_as_mlty g x)
                                     args in
                                 (uu___8, [])
                               else
                                 (let uu___9 =
                                    FStar_Compiler_Util.first_N n args in
                                  match uu___9 with
                                  | (prefix, rest) ->
                                      let uu___10 =
                                        FStar_Compiler_List.map
                                          (fun uu___11 ->
                                             match uu___11 with
                                             | (x, uu___12) ->
                                                 term_as_mlty g x) prefix in
                                      (uu___10, rest)) in
                             match uu___7 with
                             | (provided_type_args, rest) ->
                                 let uu___8 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu___9 ->
                                       let uu___10 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu___10 with
                                        | (head2, uu___11, t2) -> (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu___9 ->
                                       let uu___10 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu___10 with
                                        | (head2, uu___11, t2) -> (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,
                                        {
                                          FStar_Extraction_ML_Syntax.expr =
                                            FStar_Extraction_ML_Syntax.MLE_Const
                                            (FStar_Extraction_ML_Syntax.MLC_Unit);
                                          FStar_Extraction_ML_Syntax.mlty =
                                            uu___9;
                                          FStar_Extraction_ML_Syntax.loc =
                                            uu___10;_}::[])
                                       ->
                                       let uu___11 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args in
                                       (match uu___11 with
                                        | (head3, uu___12, t2) ->
                                            let uu___13 =
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2) in
                                            (uu___13, t2))
                                   | uu___9 ->
                                       failwith
                                         "Impossible: Unexpected head term" in
                                 (match uu___8 with
                                  | (head2, t2) -> (head2, t2, rest)) in
                           (match uu___6 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu___7 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu___7,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu___7 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | FStar_Syntax_Syntax.Tm_fvar uu___4 ->
                      let uu___5 =
                        let uu___6 =
                          FStar_Extraction_ML_UEnv.lookup_term g head1 in
                        match uu___6 with
                        | (FStar_Pervasives.Inr exp_b, q) ->
                            (FStar_Extraction_ML_UEnv.debug g
                               (fun uu___8 ->
                                  let uu___9 =
                                    FStar_Syntax_Print.term_to_string head1 in
                                  let uu___10 =
                                    let uu___11 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlexpr
                                      uu___11
                                      exp_b.FStar_Extraction_ML_UEnv.exp_b_expr in
                                  let uu___11 =
                                    let uu___12 =
                                      FStar_Extraction_ML_UEnv.current_module_of_uenv
                                        g in
                                    FStar_Extraction_ML_Code.string_of_mlty
                                      uu___12
                                      (FStar_Pervasives_Native.snd
                                         exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme) in
                                  FStar_Compiler_Util.print3
                                    "@@@looked up %s: got %s at %s\n" uu___9
                                    uu___10 uu___11);
                             (((exp_b.FStar_Extraction_ML_UEnv.exp_b_expr),
                                (exp_b.FStar_Extraction_ML_UEnv.exp_b_tscheme)),
                               q))
                        | uu___7 -> failwith "FIXME Ty" in
                      (match uu___5 with
                       | ((head_ml, (vars, t1)), qual) ->
                           let has_typ_apps =
                             match args with
                             | (a, uu___6)::uu___7 -> is_type g a
                             | uu___6 -> false in
                           let uu___6 =
                             let n = FStar_Compiler_List.length vars in
                             let uu___7 =
                               if (FStar_Compiler_List.length args) <= n
                               then
                                 let uu___8 =
                                   FStar_Compiler_List.map
                                     (fun uu___9 ->
                                        match uu___9 with
                                        | (x, uu___10) -> term_as_mlty g x)
                                     args in
                                 (uu___8, [])
                               else
                                 (let uu___9 =
                                    FStar_Compiler_Util.first_N n args in
                                  match uu___9 with
                                  | (prefix, rest) ->
                                      let uu___10 =
                                        FStar_Compiler_List.map
                                          (fun uu___11 ->
                                             match uu___11 with
                                             | (x, uu___12) ->
                                                 term_as_mlty g x) prefix in
                                      (uu___10, rest)) in
                             match uu___7 with
                             | (provided_type_args, rest) ->
                                 let uu___8 =
                                   match head_ml.FStar_Extraction_ML_Syntax.expr
                                   with
                                   | FStar_Extraction_ML_Syntax.MLE_Name
                                       uu___9 ->
                                       let uu___10 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu___10 with
                                        | (head2, uu___11, t2) -> (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_Var
                                       uu___9 ->
                                       let uu___10 =
                                         instantiate_maybe_partial g head_ml
                                           (vars, t1) provided_type_args in
                                       (match uu___10 with
                                        | (head2, uu___11, t2) -> (head2, t2))
                                   | FStar_Extraction_ML_Syntax.MLE_App
                                       (head2,
                                        {
                                          FStar_Extraction_ML_Syntax.expr =
                                            FStar_Extraction_ML_Syntax.MLE_Const
                                            (FStar_Extraction_ML_Syntax.MLC_Unit);
                                          FStar_Extraction_ML_Syntax.mlty =
                                            uu___9;
                                          FStar_Extraction_ML_Syntax.loc =
                                            uu___10;_}::[])
                                       ->
                                       let uu___11 =
                                         instantiate_maybe_partial g head2
                                           (vars, t1) provided_type_args in
                                       (match uu___11 with
                                        | (head3, uu___12, t2) ->
                                            let uu___13 =
                                              FStar_Compiler_Effect.op_Bar_Greater
                                                (FStar_Extraction_ML_Syntax.MLE_App
                                                   (head3,
                                                     [FStar_Extraction_ML_Syntax.ml_unit]))
                                                (FStar_Extraction_ML_Syntax.with_ty
                                                   t2) in
                                            (uu___13, t2))
                                   | uu___9 ->
                                       failwith
                                         "Impossible: Unexpected head term" in
                                 (match uu___8 with
                                  | (head2, t2) -> (head2, t2, rest)) in
                           (match uu___6 with
                            | (head_ml1, head_t, args1) ->
                                (match args1 with
                                 | [] ->
                                     let uu___7 =
                                       maybe_eta_data_and_project_record g
                                         qual head_t head_ml1 in
                                     (uu___7,
                                       FStar_Extraction_ML_Syntax.E_PURE,
                                       head_t)
                                 | uu___7 ->
                                     extract_app_maybe_projector qual
                                       head_ml1
                                       (FStar_Extraction_ML_Syntax.E_PURE,
                                         head_t) args1)))
                  | uu___4 ->
                      let uu___5 = term_as_mlexpr g head1 in
                      (match uu___5 with
                       | (head2, f, t1) ->
                           extract_app_maybe_projector
                             FStar_Pervasives_Native.None head2 (f, t1) args) in
                let uu___3 = is_type g t in
                if uu___3
                then
                  (FStar_Extraction_ML_Syntax.ml_unit,
                    FStar_Extraction_ML_Syntax.E_PURE,
                    FStar_Extraction_ML_Syntax.ml_unit_ty)
                else
                  (let uu___5 =
                     let uu___6 = FStar_Syntax_Util.un_uinst head in
                     uu___6.FStar_Syntax_Syntax.n in
                   match uu___5 with
                   | FStar_Syntax_Syntax.Tm_fvar fv ->
                       let uu___6 =
                         FStar_Extraction_ML_UEnv.try_lookup_fv
                           t.FStar_Syntax_Syntax.pos g fv in
                       (match uu___6 with
                        | FStar_Pervasives_Native.None ->
                            (FStar_Extraction_ML_Syntax.ml_unit,
                              FStar_Extraction_ML_Syntax.E_PURE,
                              FStar_Extraction_ML_Syntax.MLTY_Erased)
                        | uu___7 -> extract_app_with_instantiations ())
                   | uu___6 -> extract_app_with_instantiations ()))
       | FStar_Syntax_Syntax.Tm_ascribed
           { FStar_Syntax_Syntax.tm = e0;
             FStar_Syntax_Syntax.asc = (tc, uu___1, uu___2);
             FStar_Syntax_Syntax.eff_opt = f;_}
           ->
           let t1 =
             match tc with
             | FStar_Pervasives.Inl t2 -> term_as_mlty g t2
             | FStar_Pervasives.Inr c ->
                 let uu___3 =
                   let uu___4 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                   maybe_reify_comp g uu___4 c in
                 term_as_mlty g uu___3 in
           let f1 =
             match f with
             | FStar_Pervasives_Native.None ->
                 failwith "Ascription node with an empty effect label"
             | FStar_Pervasives_Native.Some l -> effect_as_etag g l in
           let uu___3 = check_term_as_mlexpr g e0 f1 t1 in
           (match uu___3 with | (e, t2) -> (e, f1, t2))
       | FStar_Syntax_Syntax.Tm_let
           { FStar_Syntax_Syntax.lbs = (false, lb::[]);
             FStar_Syntax_Syntax.body1 = e';_}
           when
           (let uu___1 = FStar_Syntax_Syntax.is_top_level [lb] in
            Prims.op_Negation uu___1) &&
             (let uu___1 =
                FStar_Syntax_Util.get_attribute
                  FStar_Parser_Const.rename_let_attr
                  lb.FStar_Syntax_Syntax.lbattrs in
              FStar_Compiler_Util.is_some uu___1)
           ->
           let b =
             let uu___1 =
               FStar_Compiler_Util.left lb.FStar_Syntax_Syntax.lbname in
             FStar_Syntax_Syntax.mk_binder uu___1 in
           let uu___1 = FStar_Syntax_Subst.open_term_1 b e' in
           (match uu___1 with
            | ({ FStar_Syntax_Syntax.binder_bv = x;
                 FStar_Syntax_Syntax.binder_qual = uu___2;
                 FStar_Syntax_Syntax.binder_positivity = uu___3;
                 FStar_Syntax_Syntax.binder_attrs = uu___4;_},
               body) ->
                let suggested_name =
                  let attr =
                    FStar_Syntax_Util.get_attribute
                      FStar_Parser_Const.rename_let_attr
                      lb.FStar_Syntax_Syntax.lbattrs in
                  match attr with
                  | FStar_Pervasives_Native.Some ((str, uu___5)::[]) ->
                      let uu___6 =
                        let uu___7 = FStar_Syntax_Subst.compress str in
                        uu___7.FStar_Syntax_Syntax.n in
                      (match uu___6 with
                       | FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_string (s, uu___7)) when
                           s <> "" ->
                           let id =
                             let uu___8 =
                               let uu___9 = FStar_Syntax_Syntax.range_of_bv x in
                               (s, uu___9) in
                             FStar_Ident.mk_ident uu___8 in
                           let bv =
                             {
                               FStar_Syntax_Syntax.ppname = id;
                               FStar_Syntax_Syntax.index = Prims.int_zero;
                               FStar_Syntax_Syntax.sort =
                                 (x.FStar_Syntax_Syntax.sort)
                             } in
                           let bv1 = FStar_Syntax_Syntax.freshen_bv bv in
                           FStar_Pervasives_Native.Some bv1
                       | uu___7 ->
                           (FStar_Errors.log_issue
                              top1.FStar_Syntax_Syntax.pos
                              (FStar_Errors_Codes.Warning_UnrecognizedAttribute,
                                "Ignoring ill-formed application of `rename_let`");
                            FStar_Pervasives_Native.None))
                  | FStar_Pervasives_Native.Some uu___5 ->
                      (FStar_Errors.log_issue top1.FStar_Syntax_Syntax.pos
                         (FStar_Errors_Codes.Warning_UnrecognizedAttribute,
                           "Ignoring ill-formed application of `rename_let`");
                       FStar_Pervasives_Native.None)
                  | FStar_Pervasives_Native.None ->
                      FStar_Pervasives_Native.None in
                let remove_attr attrs =
                  let uu___5 =
                    FStar_Compiler_List.partition
                      (fun attr ->
                         let uu___6 =
                           FStar_Syntax_Util.get_attribute
                             FStar_Parser_Const.rename_let_attr [attr] in
                         FStar_Compiler_Util.is_some uu___6)
                      lb.FStar_Syntax_Syntax.lbattrs in
                  match uu___5 with | (uu___6, other_attrs) -> other_attrs in
                let maybe_rewritten_let =
                  match suggested_name with
                  | FStar_Pervasives_Native.None ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs in
                      FStar_Syntax_Syntax.Tm_let
                        {
                          FStar_Syntax_Syntax.lbs =
                            (false,
                              [{
                                 FStar_Syntax_Syntax.lbname =
                                   (lb.FStar_Syntax_Syntax.lbname);
                                 FStar_Syntax_Syntax.lbunivs =
                                   (lb.FStar_Syntax_Syntax.lbunivs);
                                 FStar_Syntax_Syntax.lbtyp =
                                   (lb.FStar_Syntax_Syntax.lbtyp);
                                 FStar_Syntax_Syntax.lbeff =
                                   (lb.FStar_Syntax_Syntax.lbeff);
                                 FStar_Syntax_Syntax.lbdef =
                                   (lb.FStar_Syntax_Syntax.lbdef);
                                 FStar_Syntax_Syntax.lbattrs = other_attrs;
                                 FStar_Syntax_Syntax.lbpos =
                                   (lb.FStar_Syntax_Syntax.lbpos)
                               }]);
                          FStar_Syntax_Syntax.body1 = e'
                        }
                  | FStar_Pervasives_Native.Some y ->
                      let other_attrs =
                        remove_attr lb.FStar_Syntax_Syntax.lbattrs in
                      let rename =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 = FStar_Syntax_Syntax.bv_to_name y in
                            (x, uu___7) in
                          FStar_Syntax_Syntax.NT uu___6 in
                        [uu___5] in
                      let body1 =
                        let uu___5 =
                          let uu___6 = FStar_Syntax_Syntax.mk_binder y in
                          [uu___6] in
                        let uu___6 = FStar_Syntax_Subst.subst rename body in
                        FStar_Syntax_Subst.close uu___5 uu___6 in
                      let lb1 =
                        {
                          FStar_Syntax_Syntax.lbname =
                            (FStar_Pervasives.Inl y);
                          FStar_Syntax_Syntax.lbunivs =
                            (lb.FStar_Syntax_Syntax.lbunivs);
                          FStar_Syntax_Syntax.lbtyp =
                            (lb.FStar_Syntax_Syntax.lbtyp);
                          FStar_Syntax_Syntax.lbeff =
                            (lb.FStar_Syntax_Syntax.lbeff);
                          FStar_Syntax_Syntax.lbdef =
                            (lb.FStar_Syntax_Syntax.lbdef);
                          FStar_Syntax_Syntax.lbattrs = other_attrs;
                          FStar_Syntax_Syntax.lbpos =
                            (lb.FStar_Syntax_Syntax.lbpos)
                        } in
                      FStar_Syntax_Syntax.Tm_let
                        {
                          FStar_Syntax_Syntax.lbs = (false, [lb1]);
                          FStar_Syntax_Syntax.body1 = body1
                        } in
                let top2 =
                  {
                    FStar_Syntax_Syntax.n = maybe_rewritten_let;
                    FStar_Syntax_Syntax.pos = (top1.FStar_Syntax_Syntax.pos);
                    FStar_Syntax_Syntax.vars =
                      (top1.FStar_Syntax_Syntax.vars);
                    FStar_Syntax_Syntax.hash_code =
                      (top1.FStar_Syntax_Syntax.hash_code)
                  } in
                term_as_mlexpr' g top2)
       | FStar_Syntax_Syntax.Tm_let
           { FStar_Syntax_Syntax.lbs = (is_rec, lbs);
             FStar_Syntax_Syntax.body1 = e';_}
           ->
           let top_level = FStar_Syntax_Syntax.is_top_level lbs in
           let uu___1 =
             if is_rec
             then FStar_Syntax_Subst.open_let_rec lbs e'
             else
               (let uu___3 = FStar_Syntax_Syntax.is_top_level lbs in
                if uu___3
                then (lbs, e')
                else
                  (let lb = FStar_Compiler_List.hd lbs in
                   let x =
                     let uu___5 =
                       FStar_Compiler_Util.left lb.FStar_Syntax_Syntax.lbname in
                     FStar_Syntax_Syntax.freshen_bv uu___5 in
                   let lb1 =
                     {
                       FStar_Syntax_Syntax.lbname = (FStar_Pervasives.Inl x);
                       FStar_Syntax_Syntax.lbunivs =
                         (lb.FStar_Syntax_Syntax.lbunivs);
                       FStar_Syntax_Syntax.lbtyp =
                         (lb.FStar_Syntax_Syntax.lbtyp);
                       FStar_Syntax_Syntax.lbeff =
                         (lb.FStar_Syntax_Syntax.lbeff);
                       FStar_Syntax_Syntax.lbdef =
                         (lb.FStar_Syntax_Syntax.lbdef);
                       FStar_Syntax_Syntax.lbattrs =
                         (lb.FStar_Syntax_Syntax.lbattrs);
                       FStar_Syntax_Syntax.lbpos =
                         (lb.FStar_Syntax_Syntax.lbpos)
                     } in
                   let e'1 =
                     FStar_Syntax_Subst.subst
                       [FStar_Syntax_Syntax.DB (Prims.int_zero, x)] e' in
                   ([lb1], e'1))) in
           (match uu___1 with
            | (lbs1, e'1) ->
                let lbs2 =
                  if top_level
                  then
                    let tcenv =
                      let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                      let uu___3 =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              FStar_Extraction_ML_UEnv.current_module_of_uenv
                                g in
                            FStar_Pervasives_Native.fst uu___6 in
                          let uu___6 =
                            let uu___7 =
                              let uu___8 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              FStar_Pervasives_Native.snd uu___8 in
                            [uu___7] in
                          FStar_Compiler_List.op_At uu___5 uu___6 in
                        FStar_Ident.lid_of_path uu___4
                          FStar_Compiler_Range_Type.dummyRange in
                      FStar_TypeChecker_Env.set_current_module uu___2 uu___3 in
                    FStar_Compiler_Effect.op_Bar_Greater lbs1
                      (FStar_Compiler_List.map
                         (fun lb ->
                            let lbdef =
                              let uu___2 = FStar_Options.ml_ish () in
                              if uu___2
                              then lb.FStar_Syntax_Syntax.lbdef
                              else
                                (let norm_call uu___4 =
                                   let uu___5 =
                                     let uu___6 =
                                       let uu___7 =
                                         FStar_TypeChecker_Env.current_module
                                           tcenv in
                                       FStar_Ident.string_of_lid uu___7 in
                                     FStar_Pervasives_Native.Some uu___6 in
                                   FStar_Profiling.profile
                                     (fun uu___6 ->
                                        FStar_TypeChecker_Normalize.normalize
                                          (FStar_TypeChecker_Env.PureSubtermsWithinComputations
                                          :: FStar_TypeChecker_Env.Reify ::
                                          extraction_norm_steps) tcenv
                                          lb.FStar_Syntax_Syntax.lbdef)
                                     uu___5
                                     "FStar.Extraction.ML.Term.normalize_lb_def" in
                                 let uu___4 =
                                   (FStar_Compiler_Effect.op_Less_Bar
                                      (FStar_TypeChecker_Env.debug tcenv)
                                      (FStar_Options.Other "Extraction"))
                                     ||
                                     (FStar_Compiler_Effect.op_Less_Bar
                                        (FStar_TypeChecker_Env.debug tcenv)
                                        (FStar_Options.Other "ExtractNorm")) in
                                 if uu___4
                                 then
                                   ((let uu___6 =
                                       FStar_Syntax_Print.lbname_to_string
                                         lb.FStar_Syntax_Syntax.lbname in
                                     let uu___7 =
                                       FStar_Syntax_Print.term_to_string
                                         lb.FStar_Syntax_Syntax.lbdef in
                                     FStar_Compiler_Util.print2
                                       "Starting to normalize top-level let %s = %s\n"
                                       uu___6 uu___7);
                                    (let a = norm_call () in
                                     (let uu___7 =
                                        FStar_Syntax_Print.term_to_string a in
                                      FStar_Compiler_Util.print1
                                        "Normalized to %s\n" uu___7);
                                     a))
                                 else norm_call ()) in
                            {
                              FStar_Syntax_Syntax.lbname =
                                (lb.FStar_Syntax_Syntax.lbname);
                              FStar_Syntax_Syntax.lbunivs =
                                (lb.FStar_Syntax_Syntax.lbunivs);
                              FStar_Syntax_Syntax.lbtyp =
                                (lb.FStar_Syntax_Syntax.lbtyp);
                              FStar_Syntax_Syntax.lbeff =
                                (lb.FStar_Syntax_Syntax.lbeff);
                              FStar_Syntax_Syntax.lbdef = lbdef;
                              FStar_Syntax_Syntax.lbattrs =
                                (lb.FStar_Syntax_Syntax.lbattrs);
                              FStar_Syntax_Syntax.lbpos =
                                (lb.FStar_Syntax_Syntax.lbpos)
                            }))
                  else lbs1 in
                let check_lb env uu___2 =
                  match uu___2 with
                  | (nm, (_lbname, f, (_t, (targs, polytype)), add_unit, e))
                      ->
                      let env1 =
                        FStar_Compiler_List.fold_left
                          (fun env2 ->
                             fun uu___3 ->
                               match uu___3 with
                               | { FStar_Syntax_Syntax.binder_bv = a;
                                   FStar_Syntax_Syntax.binder_qual = uu___4;
                                   FStar_Syntax_Syntax.binder_positivity =
                                     uu___5;
                                   FStar_Syntax_Syntax.binder_attrs = uu___6;_}
                                   ->
                                   FStar_Extraction_ML_UEnv.extend_ty env2 a
                                     false) env targs in
                      let expected_t = FStar_Pervasives_Native.snd polytype in
                      let uu___3 = check_term_as_mlexpr env1 e f expected_t in
                      (match uu___3 with
                       | (e1, ty) ->
                           let uu___4 = maybe_promote_effect e1 f expected_t in
                           (match uu___4 with
                            | (e2, f1) ->
                                let meta =
                                  match (f1, ty) with
                                  | (FStar_Extraction_ML_Syntax.E_PURE,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | (FStar_Extraction_ML_Syntax.E_ERASABLE,
                                     FStar_Extraction_ML_Syntax.MLTY_Erased)
                                      -> [FStar_Extraction_ML_Syntax.Erased]
                                  | uu___5 -> [] in
                                (f1,
                                  {
                                    FStar_Extraction_ML_Syntax.mllb_name = nm;
                                    FStar_Extraction_ML_Syntax.mllb_tysc =
                                      (FStar_Pervasives_Native.Some polytype);
                                    FStar_Extraction_ML_Syntax.mllb_add_unit
                                      = add_unit;
                                    FStar_Extraction_ML_Syntax.mllb_def = e2;
                                    FStar_Extraction_ML_Syntax.mllb_meta =
                                      meta;
                                    FStar_Extraction_ML_Syntax.print_typ =
                                      true
                                  }))) in
                let lbs3 = extract_lb_sig g (is_rec, lbs2) in
                let uu___2 =
                  FStar_Compiler_List.fold_right
                    (fun lb ->
                       fun uu___3 ->
                         match uu___3 with
                         | (env, lbs4, env_burn) ->
                             let uu___4 = lb in
                             (match uu___4 with
                              | (lbname, uu___5, (t1, (uu___6, polytype)),
                                 add_unit, uu___7) ->
                                  let uu___8 =
                                    FStar_Extraction_ML_UEnv.extend_lb env
                                      lbname t1 polytype add_unit in
                                  (match uu___8 with
                                   | (env1, nm, uu___9) ->
                                       let env_burn1 =
                                         let uu___10 =
                                           let uu___11 =
                                             FStar_Options.codegen () in
                                           uu___11 <>
                                             (FStar_Pervasives_Native.Some
                                                FStar_Options.Krml) in
                                         if uu___10
                                         then
                                           FStar_Extraction_ML_UEnv.burn_name
                                             env_burn nm
                                         else env_burn in
                                       (env1, ((nm, lb) :: lbs4), env_burn1))))
                    lbs3 (g, [], g) in
                (match uu___2 with
                 | (env_body, lbs4, env_burn) ->
                     let env_def = if is_rec then env_body else env_burn in
                     let lbs5 =
                       FStar_Compiler_Effect.op_Bar_Greater lbs4
                         (FStar_Compiler_List.map (check_lb env_def)) in
                     let e'_rng = e'1.FStar_Syntax_Syntax.pos in
                     let uu___3 = term_as_mlexpr env_body e'1 in
                     (match uu___3 with
                      | (e'2, f', t') ->
                          let f =
                            let uu___4 =
                              let uu___5 =
                                FStar_Compiler_List.map
                                  FStar_Pervasives_Native.fst lbs5 in
                              f' :: uu___5 in
                            FStar_Extraction_ML_Util.join_l e'_rng uu___4 in
                          let is_rec1 =
                            if is_rec = true
                            then FStar_Extraction_ML_Syntax.Rec
                            else FStar_Extraction_ML_Syntax.NonRec in
                          let uu___4 =
                            let uu___5 =
                              let uu___6 =
                                let uu___7 =
                                  FStar_Compiler_List.map
                                    FStar_Pervasives_Native.snd lbs5 in
                                (is_rec1, uu___7) in
                              mk_MLE_Let top_level uu___6 e'2 in
                            let uu___6 =
                              FStar_Extraction_ML_Util.mlloc_of_range
                                t.FStar_Syntax_Syntax.pos in
                            FStar_Extraction_ML_Syntax.with_ty_loc t' uu___5
                              uu___6 in
                          (uu___4, f, t'))))
       | FStar_Syntax_Syntax.Tm_match
           { FStar_Syntax_Syntax.scrutinee = scrutinee;
             FStar_Syntax_Syntax.ret_opt = uu___1;
             FStar_Syntax_Syntax.brs = pats;
             FStar_Syntax_Syntax.rc_opt1 = uu___2;_}
           ->
           let uu___3 = term_as_mlexpr g scrutinee in
           (match uu___3 with
            | (e, f_e, t_e) ->
                let uu___4 = check_pats_for_ite pats in
                (match uu___4 with
                 | (b, then_e, else_e) ->
                     let no_lift x t1 = x in
                     if b
                     then
                       (match (then_e, else_e) with
                        | (FStar_Pervasives_Native.Some then_e1,
                           FStar_Pervasives_Native.Some else_e1) ->
                            let uu___5 = term_as_mlexpr g then_e1 in
                            (match uu___5 with
                             | (then_mle, f_then, t_then) ->
                                 let uu___6 = term_as_mlexpr g else_e1 in
                                 (match uu___6 with
                                  | (else_mle, f_else, t_else) ->
                                      let uu___7 =
                                        let uu___8 = type_leq g t_then t_else in
                                        if uu___8
                                        then (t_else, no_lift)
                                        else
                                          (let uu___10 =
                                             type_leq g t_else t_then in
                                           if uu___10
                                           then (t_then, no_lift)
                                           else
                                             (FStar_Extraction_ML_Syntax.MLTY_Top,
                                               FStar_Extraction_ML_Syntax.apply_obj_repr)) in
                                      (match uu___7 with
                                       | (t_branch, maybe_lift) ->
                                           let uu___8 =
                                             let uu___9 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   maybe_lift then_mle t_then in
                                                 let uu___12 =
                                                   let uu___13 =
                                                     maybe_lift else_mle
                                                       t_else in
                                                   FStar_Pervasives_Native.Some
                                                     uu___13 in
                                                 (e, uu___11, uu___12) in
                                               FStar_Extraction_ML_Syntax.MLE_If
                                                 uu___10 in
                                             FStar_Compiler_Effect.op_Less_Bar
                                               (FStar_Extraction_ML_Syntax.with_ty
                                                  t_branch) uu___9 in
                                           let uu___9 =
                                             FStar_Extraction_ML_Util.join
                                               then_e1.FStar_Syntax_Syntax.pos
                                               f_then f_else in
                                           (uu___8, uu___9, t_branch))))
                        | uu___5 ->
                            failwith
                              "ITE pats matched but then and else expressions not found?")
                     else
                       (let uu___6 =
                          FStar_Compiler_Effect.op_Bar_Greater pats
                            (FStar_Compiler_Util.fold_map
                               (fun compat ->
                                  fun br ->
                                    let uu___7 =
                                      FStar_Syntax_Subst.open_branch br in
                                    match uu___7 with
                                    | (pat, when_opt, branch) ->
                                        let uu___8 =
                                          extract_pat g pat t_e
                                            term_as_mlexpr in
                                        (match uu___8 with
                                         | (env, p, pat_t_compat) ->
                                             let uu___9 =
                                               match when_opt with
                                               | FStar_Pervasives_Native.None
                                                   ->
                                                   (FStar_Pervasives_Native.None,
                                                     FStar_Extraction_ML_Syntax.E_PURE)
                                               | FStar_Pervasives_Native.Some
                                                   w ->
                                                   let w_pos =
                                                     w.FStar_Syntax_Syntax.pos in
                                                   let uu___10 =
                                                     term_as_mlexpr env w in
                                                   (match uu___10 with
                                                    | (w1, f_w, t_w) ->
                                                        let w2 =
                                                          maybe_coerce w_pos
                                                            env w1 t_w
                                                            FStar_Extraction_ML_Syntax.ml_bool_ty in
                                                        ((FStar_Pervasives_Native.Some
                                                            w2), f_w)) in
                                             (match uu___9 with
                                              | (when_opt1, f_when) ->
                                                  let uu___10 =
                                                    term_as_mlexpr env branch in
                                                  (match uu___10 with
                                                   | (mlbranch, f_branch,
                                                      t_branch) ->
                                                       let uu___11 =
                                                         FStar_Compiler_Effect.op_Bar_Greater
                                                           p
                                                           (FStar_Compiler_List.map
                                                              (fun uu___12 ->
                                                                 match uu___12
                                                                 with
                                                                 | (p1, wopt)
                                                                    ->
                                                                    let when_clause
                                                                    =
                                                                    FStar_Extraction_ML_Util.conjoin_opt
                                                                    wopt
                                                                    when_opt1 in
                                                                    (p1,
                                                                    (when_clause,
                                                                    f_when),
                                                                    (mlbranch,
                                                                    f_branch,
                                                                    t_branch)))) in
                                                       ((compat &&
                                                           pat_t_compat),
                                                         uu___11))))) true) in
                        match uu___6 with
                        | (pat_t_compat, mlbranches) ->
                            let mlbranches1 =
                              FStar_Compiler_List.flatten mlbranches in
                            let e1 =
                              if pat_t_compat
                              then e
                              else
                                (FStar_Extraction_ML_UEnv.debug g
                                   (fun uu___9 ->
                                      let uu___10 =
                                        let uu___11 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g in
                                        FStar_Extraction_ML_Code.string_of_mlexpr
                                          uu___11 e in
                                      let uu___11 =
                                        let uu___12 =
                                          FStar_Extraction_ML_UEnv.current_module_of_uenv
                                            g in
                                        FStar_Extraction_ML_Code.string_of_mlty
                                          uu___12 t_e in
                                      FStar_Compiler_Util.print2
                                        "Coercing scrutinee %s from type %s because pattern type is incompatible\n"
                                        uu___10 uu___11);
                                 FStar_Compiler_Effect.op_Less_Bar
                                   (FStar_Extraction_ML_Syntax.with_ty t_e)
                                   (FStar_Extraction_ML_Syntax.MLE_Coerce
                                      (e, t_e,
                                        FStar_Extraction_ML_Syntax.MLTY_Top))) in
                            (match mlbranches1 with
                             | [] ->
                                 let uu___7 =
                                   let uu___8 =
                                     let uu___9 =
                                       FStar_Parser_Const.failwith_lid () in
                                     FStar_Syntax_Syntax.lid_as_fv uu___9
                                       FStar_Pervasives_Native.None in
                                   FStar_Extraction_ML_UEnv.lookup_fv
                                     t.FStar_Syntax_Syntax.pos g uu___8 in
                                 (match uu___7 with
                                  | {
                                      FStar_Extraction_ML_UEnv.exp_b_name =
                                        uu___8;
                                      FStar_Extraction_ML_UEnv.exp_b_expr =
                                        fw;
                                      FStar_Extraction_ML_UEnv.exp_b_tscheme
                                        = uu___9;_}
                                      ->
                                      let uu___10 =
                                        let uu___11 =
                                          let uu___12 =
                                            let uu___13 =
                                              let uu___14 =
                                                FStar_Compiler_Effect.op_Less_Bar
                                                  (FStar_Extraction_ML_Syntax.with_ty
                                                     FStar_Extraction_ML_Syntax.ml_string_ty)
                                                  (FStar_Extraction_ML_Syntax.MLE_Const
                                                     (FStar_Extraction_ML_Syntax.MLC_String
                                                        "unreachable")) in
                                              [uu___14] in
                                            (fw, uu___13) in
                                          FStar_Extraction_ML_Syntax.MLE_App
                                            uu___12 in
                                        FStar_Compiler_Effect.op_Less_Bar
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_int_ty)
                                          uu___11 in
                                      (uu___10,
                                        FStar_Extraction_ML_Syntax.E_PURE,
                                        FStar_Extraction_ML_Syntax.ml_int_ty))
                             | (uu___7, uu___8, (uu___9, f_first, t_first))::rest
                                 ->
                                 let uu___10 =
                                   FStar_Compiler_List.fold_left
                                     (fun uu___11 ->
                                        fun uu___12 ->
                                          match (uu___11, uu___12) with
                                          | ((topt, f),
                                             (uu___13, uu___14,
                                              (uu___15, f_branch, t_branch)))
                                              ->
                                              let f1 =
                                                FStar_Extraction_ML_Util.join
                                                  top1.FStar_Syntax_Syntax.pos
                                                  f f_branch in
                                              let topt1 =
                                                match topt with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Pervasives_Native.None
                                                | FStar_Pervasives_Native.Some
                                                    t1 ->
                                                    let uu___16 =
                                                      type_leq g t1 t_branch in
                                                    if uu___16
                                                    then
                                                      FStar_Pervasives_Native.Some
                                                        t_branch
                                                    else
                                                      (let uu___18 =
                                                         type_leq g t_branch
                                                           t1 in
                                                       if uu___18
                                                       then
                                                         FStar_Pervasives_Native.Some
                                                           t1
                                                       else
                                                         FStar_Pervasives_Native.None) in
                                              (topt1, f1))
                                     ((FStar_Pervasives_Native.Some t_first),
                                       f_first) rest in
                                 (match uu___10 with
                                  | (topt, f_match) ->
                                      let mlbranches2 =
                                        FStar_Compiler_Effect.op_Bar_Greater
                                          mlbranches1
                                          (FStar_Compiler_List.map
                                             (fun uu___11 ->
                                                match uu___11 with
                                                | (p, (wopt, uu___12),
                                                   (b1, uu___13, t1)) ->
                                                    let b2 =
                                                      match topt with
                                                      | FStar_Pervasives_Native.None
                                                          ->
                                                          FStar_Extraction_ML_Syntax.apply_obj_repr
                                                            b1 t1
                                                      | FStar_Pervasives_Native.Some
                                                          uu___14 -> b1 in
                                                    (p, wopt, b2))) in
                                      let t_match =
                                        match topt with
                                        | FStar_Pervasives_Native.None ->
                                            FStar_Extraction_ML_Syntax.MLTY_Top
                                        | FStar_Pervasives_Native.Some t1 ->
                                            t1 in
                                      let uu___11 =
                                        FStar_Compiler_Effect.op_Less_Bar
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             t_match)
                                          (FStar_Extraction_ML_Syntax.MLE_Match
                                             (e1, mlbranches2)) in
                                      (uu___11, f_match, t_match)))))))
let (ind_discriminator_body :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Ident.lident ->
      FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlmodule1)
  =
  fun env ->
    fun discName ->
      fun constrName ->
        let uu___ =
          let uu___1 =
            let uu___2 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStar_TypeChecker_Env.lookup_lid uu___2 discName in
          FStar_Compiler_Effect.op_Less_Bar FStar_Pervasives_Native.fst
            uu___1 in
        match uu___ with
        | (uu___1, fstar_disc_type) ->
            let uu___2 =
              let uu___3 =
                let uu___4 = FStar_Syntax_Subst.compress fstar_disc_type in
                uu___4.FStar_Syntax_Syntax.n in
              match uu___3 with
              | FStar_Syntax_Syntax.Tm_arrow
                  { FStar_Syntax_Syntax.bs1 = binders;
                    FStar_Syntax_Syntax.comp = uu___4;_}
                  ->
                  let binders1 =
                    FStar_Compiler_Effect.op_Bar_Greater binders
                      (FStar_Compiler_List.filter
                         (fun uu___5 ->
                            match uu___5 with
                            | { FStar_Syntax_Syntax.binder_bv = uu___6;
                                FStar_Syntax_Syntax.binder_qual =
                                  FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Syntax.Implicit uu___7);
                                FStar_Syntax_Syntax.binder_positivity =
                                  uu___8;
                                FStar_Syntax_Syntax.binder_attrs = uu___9;_}
                                -> true
                            | uu___6 -> false)) in
                  FStar_Compiler_List.fold_right
                    (fun uu___5 ->
                       fun uu___6 ->
                         match uu___6 with
                         | (g, vs) ->
                             let uu___7 =
                               FStar_Extraction_ML_UEnv.new_mlident g in
                             (match uu___7 with
                              | (g1, v) ->
                                  (g1,
                                    ((v, FStar_Extraction_ML_Syntax.MLTY_Top)
                                    :: vs)))) binders1 (env, [])
              | uu___4 -> failwith "Discriminator must be a function" in
            (match uu___2 with
             | (g, wildcards) ->
                 let uu___3 = FStar_Extraction_ML_UEnv.new_mlident g in
                 (match uu___3 with
                  | (g1, mlid) ->
                      let targ = FStar_Extraction_ML_Syntax.MLTY_Top in
                      let disc_ty = FStar_Extraction_ML_Syntax.MLTY_Top in
                      let discrBody =
                        let uu___4 =
                          let uu___5 =
                            let uu___6 =
                              let uu___7 =
                                let uu___8 =
                                  let uu___9 =
                                    FStar_Compiler_Effect.op_Less_Bar
                                      (FStar_Extraction_ML_Syntax.with_ty
                                         targ)
                                      (FStar_Extraction_ML_Syntax.MLE_Name
                                         ([], mlid)) in
                                  let uu___10 =
                                    let uu___11 =
                                      let uu___12 =
                                        let uu___13 =
                                          let uu___14 =
                                            FStar_Extraction_ML_UEnv.mlpath_of_lident
                                              g1 constrName in
                                          (uu___14,
                                            [FStar_Extraction_ML_Syntax.MLP_Wild]) in
                                        FStar_Extraction_ML_Syntax.MLP_CTor
                                          uu___13 in
                                      let uu___13 =
                                        FStar_Compiler_Effect.op_Less_Bar
                                          (FStar_Extraction_ML_Syntax.with_ty
                                             FStar_Extraction_ML_Syntax.ml_bool_ty)
                                          (FStar_Extraction_ML_Syntax.MLE_Const
                                             (FStar_Extraction_ML_Syntax.MLC_Bool
                                                true)) in
                                      (uu___12, FStar_Pervasives_Native.None,
                                        uu___13) in
                                    let uu___12 =
                                      let uu___13 =
                                        let uu___14 =
                                          FStar_Compiler_Effect.op_Less_Bar
                                            (FStar_Extraction_ML_Syntax.with_ty
                                               FStar_Extraction_ML_Syntax.ml_bool_ty)
                                            (FStar_Extraction_ML_Syntax.MLE_Const
                                               (FStar_Extraction_ML_Syntax.MLC_Bool
                                                  false)) in
                                        (FStar_Extraction_ML_Syntax.MLP_Wild,
                                          FStar_Pervasives_Native.None,
                                          uu___14) in
                                      [uu___13] in
                                    uu___11 :: uu___12 in
                                  (uu___9, uu___10) in
                                FStar_Extraction_ML_Syntax.MLE_Match uu___8 in
                              FStar_Compiler_Effect.op_Less_Bar
                                (FStar_Extraction_ML_Syntax.with_ty
                                   FStar_Extraction_ML_Syntax.ml_bool_ty)
                                uu___7 in
                            ((FStar_Compiler_List.op_At wildcards
                                [(mlid, targ)]), uu___6) in
                          FStar_Extraction_ML_Syntax.MLE_Fun uu___5 in
                        FStar_Compiler_Effect.op_Less_Bar
                          (FStar_Extraction_ML_Syntax.with_ty disc_ty) uu___4 in
                      let uu___4 =
                        FStar_Extraction_ML_UEnv.mlpath_of_lident env
                          discName in
                      (match uu___4 with
                       | (uu___5, name) ->
                           FStar_Extraction_ML_Syntax.MLM_Let
                             (FStar_Extraction_ML_Syntax.NonRec,
                               [{
                                  FStar_Extraction_ML_Syntax.mllb_name = name;
                                  FStar_Extraction_ML_Syntax.mllb_tysc =
                                    FStar_Pervasives_Native.None;
                                  FStar_Extraction_ML_Syntax.mllb_add_unit =
                                    false;
                                  FStar_Extraction_ML_Syntax.mllb_def =
                                    discrBody;
                                  FStar_Extraction_ML_Syntax.mllb_meta = [];
                                  FStar_Extraction_ML_Syntax.print_typ =
                                    false
                                }]))))