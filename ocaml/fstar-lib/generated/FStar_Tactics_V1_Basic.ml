open Prims
let (core_check :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term ->
        Prims.bool ->
          (FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option,
            FStar_TypeChecker_Core.error) FStar_Pervasives.either)
  =
  fun env ->
    fun sol ->
      fun t ->
        fun must_tot ->
          let uu___ =
            let uu___1 = FStar_Options.compat_pre_core_should_check () in
            Prims.op_Negation uu___1 in
          if uu___
          then FStar_Pervasives.Inl FStar_Pervasives_Native.None
          else
            (let debug f =
               let uu___2 = FStar_Options.debug_any () in
               if uu___2 then f () else () in
             let uu___2 =
               FStar_TypeChecker_Core.check_term env sol t must_tot in
             match uu___2 with
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.None) ->
                 FStar_Pervasives.Inl FStar_Pervasives_Native.None
             | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g) ->
                 let uu___3 = FStar_Options.compat_pre_core_set () in
                 if uu___3
                 then FStar_Pervasives.Inl FStar_Pervasives_Native.None
                 else FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g)
             | FStar_Pervasives.Inr err ->
                 (debug
                    (fun uu___4 ->
                       let uu___5 =
                         let uu___6 = FStar_TypeChecker_Env.get_range env in
                         FStar_Compiler_Range_Ops.string_of_range uu___6 in
                       let uu___6 =
                         FStar_TypeChecker_Core.print_error_short err in
                       let uu___7 = FStar_Syntax_Print.term_to_string sol in
                       let uu___8 = FStar_Syntax_Print.term_to_string t in
                       let uu___9 = FStar_TypeChecker_Core.print_error err in
                       FStar_Compiler_Util.print5
                         "(%s) Core checking failed (%s) on term %s and type %s\n%s\n"
                         uu___5 uu___6 uu___7 uu___8 uu___9);
                  FStar_Pervasives.Inr err))
type name = FStar_Syntax_Syntax.bv
type env = FStar_TypeChecker_Env.env
type implicits = FStar_TypeChecker_Env.implicits
let (rangeof : FStar_Tactics_Types.goal -> FStar_Compiler_Range_Type.range) =
  fun g ->
    (g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_range
let (normalize :
  FStar_TypeChecker_Env.steps ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  =
  fun s ->
    fun e ->
      fun t ->
        FStar_TypeChecker_Normalize.normalize_with_primitive_steps
          FStar_Reflection_V1_Interpreter.reflection_primops s e t
let (bnorm :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> normalize [] e t
let (whnf :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term)
  = fun e -> fun t -> FStar_TypeChecker_Normalize.unfold_whnf e t
let (tts :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.string) =
  FStar_TypeChecker_Normalize.term_to_string
let (set_uvar_expected_typ :
  FStar_Syntax_Syntax.ctx_uvar -> FStar_Syntax_Syntax.typ -> unit) =
  fun u ->
    fun t ->
      let dec =
        FStar_Syntax_Unionfind.find_decoration
          u.FStar_Syntax_Syntax.ctx_uvar_head in
      FStar_Syntax_Unionfind.change_decoration
        u.FStar_Syntax_Syntax.ctx_uvar_head
        {
          FStar_Syntax_Syntax.uvar_decoration_typ = t;
          FStar_Syntax_Syntax.uvar_decoration_typedness_depends_on =
            (dec.FStar_Syntax_Syntax.uvar_decoration_typedness_depends_on);
          FStar_Syntax_Syntax.uvar_decoration_should_check =
            (dec.FStar_Syntax_Syntax.uvar_decoration_should_check)
        }
let (mark_uvar_with_should_check_tag :
  FStar_Syntax_Syntax.ctx_uvar ->
    FStar_Syntax_Syntax.should_check_uvar -> unit)
  =
  fun u ->
    fun sc ->
      let dec =
        FStar_Syntax_Unionfind.find_decoration
          u.FStar_Syntax_Syntax.ctx_uvar_head in
      FStar_Syntax_Unionfind.change_decoration
        u.FStar_Syntax_Syntax.ctx_uvar_head
        {
          FStar_Syntax_Syntax.uvar_decoration_typ =
            (dec.FStar_Syntax_Syntax.uvar_decoration_typ);
          FStar_Syntax_Syntax.uvar_decoration_typedness_depends_on =
            (dec.FStar_Syntax_Syntax.uvar_decoration_typedness_depends_on);
          FStar_Syntax_Syntax.uvar_decoration_should_check = sc
        }
let (mark_uvar_as_already_checked : FStar_Syntax_Syntax.ctx_uvar -> unit) =
  fun u ->
    mark_uvar_with_should_check_tag u FStar_Syntax_Syntax.Already_checked
let (mark_goal_implicit_already_checked : FStar_Tactics_Types.goal -> unit) =
  fun g -> mark_uvar_as_already_checked g.FStar_Tactics_Types.goal_ctx_uvar
let (goal_with_type :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.typ -> FStar_Tactics_Types.goal)
  =
  fun g ->
    fun t ->
      let u = g.FStar_Tactics_Types.goal_ctx_uvar in
      set_uvar_expected_typ u t; g
let (bnorm_goal : FStar_Tactics_Types.goal -> FStar_Tactics_Types.goal) =
  fun g ->
    let uu___ =
      let uu___1 = FStar_Tactics_Types.goal_env g in
      let uu___2 = FStar_Tactics_Types.goal_type g in bnorm uu___1 uu___2 in
    goal_with_type g uu___
let (tacprint : Prims.string -> unit) =
  fun s -> FStar_Compiler_Util.print1 "TAC>> %s\n" s
let (tacprint1 : Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      let uu___ = FStar_Compiler_Util.format1 s x in
      FStar_Compiler_Util.print1 "TAC>> %s\n" uu___
let (tacprint2 : Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        let uu___ = FStar_Compiler_Util.format2 s x y in
        FStar_Compiler_Util.print1 "TAC>> %s\n" uu___
let (tacprint3 :
  Prims.string -> Prims.string -> Prims.string -> Prims.string -> unit) =
  fun s ->
    fun x ->
      fun y ->
        fun z ->
          let uu___ = FStar_Compiler_Util.format3 s x y z in
          FStar_Compiler_Util.print1 "TAC>> %s\n" uu___
let (print : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    (let uu___1 =
       let uu___2 = FStar_Options.silent () in Prims.op_Negation uu___2 in
     if uu___1 then tacprint msg else ());
    FStar_Tactics_Monad.ret ()
let (debugging : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let uu___1 =
           FStar_TypeChecker_Env.debug ps.FStar_Tactics_Types.main_context
             (FStar_Options.Other "Tac") in
         FStar_Tactics_Monad.ret uu___1)
let (do_dump_ps : Prims.string -> FStar_Tactics_Types.proofstate -> unit) =
  fun msg ->
    fun ps ->
      let psc = ps.FStar_Tactics_Types.psc in
      let subst = FStar_TypeChecker_Cfg.psc_subst psc in
      FStar_Tactics_Printing.do_dump_proofstate ps msg
let (dump : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun msg ->
    FStar_Tactics_Monad.mk_tac
      (fun ps -> do_dump_ps msg ps; FStar_Tactics_Result.Success ((), ps))
let (dump_all : Prims.bool -> Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun print_resolved ->
    fun msg ->
      FStar_Tactics_Monad.mk_tac
        (fun ps ->
           let gs =
             FStar_Compiler_List.map
               (fun i ->
                  FStar_Tactics_Types.goal_of_implicit
                    ps.FStar_Tactics_Types.main_context i)
               ps.FStar_Tactics_Types.all_implicits in
           let gs1 =
             if print_resolved
             then gs
             else
               FStar_Compiler_List.filter
                 (fun g ->
                    let uu___1 = FStar_Tactics_Types.check_goal_solved g in
                    Prims.op_Negation uu___1) gs in
           let ps' =
             {
               FStar_Tactics_Types.main_context =
                 (ps.FStar_Tactics_Types.main_context);
               FStar_Tactics_Types.all_implicits =
                 (ps.FStar_Tactics_Types.all_implicits);
               FStar_Tactics_Types.goals = gs1;
               FStar_Tactics_Types.smt_goals = [];
               FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
               FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
               FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
               FStar_Tactics_Types.entry_range =
                 (ps.FStar_Tactics_Types.entry_range);
               FStar_Tactics_Types.guard_policy =
                 (ps.FStar_Tactics_Types.guard_policy);
               FStar_Tactics_Types.freshness =
                 (ps.FStar_Tactics_Types.freshness);
               FStar_Tactics_Types.tac_verb_dbg =
                 (ps.FStar_Tactics_Types.tac_verb_dbg);
               FStar_Tactics_Types.local_state =
                 (ps.FStar_Tactics_Types.local_state);
               FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
             } in
           do_dump_ps msg ps'; FStar_Tactics_Result.Success ((), ps))
let (dump_uvars_of :
  FStar_Tactics_Types.goal -> Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun g ->
    fun msg ->
      FStar_Tactics_Monad.mk_tac
        (fun ps ->
           let uvs =
             let uu___ =
               let uu___1 = FStar_Tactics_Types.goal_type g in
               FStar_Syntax_Free.uvars uu___1 in
             FStar_Compiler_Effect.op_Bar_Greater uu___
               FStar_Compiler_Util.set_elements in
           let gs =
             FStar_Compiler_List.map (FStar_Tactics_Types.goal_of_ctx_uvar g)
               uvs in
           let gs1 =
             FStar_Compiler_List.filter
               (fun g1 ->
                  let uu___ = FStar_Tactics_Types.check_goal_solved g1 in
                  Prims.op_Negation uu___) gs in
           let ps' =
             {
               FStar_Tactics_Types.main_context =
                 (ps.FStar_Tactics_Types.main_context);
               FStar_Tactics_Types.all_implicits =
                 (ps.FStar_Tactics_Types.all_implicits);
               FStar_Tactics_Types.goals = gs1;
               FStar_Tactics_Types.smt_goals = [];
               FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
               FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
               FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
               FStar_Tactics_Types.entry_range =
                 (ps.FStar_Tactics_Types.entry_range);
               FStar_Tactics_Types.guard_policy =
                 (ps.FStar_Tactics_Types.guard_policy);
               FStar_Tactics_Types.freshness =
                 (ps.FStar_Tactics_Types.freshness);
               FStar_Tactics_Types.tac_verb_dbg =
                 (ps.FStar_Tactics_Types.tac_verb_dbg);
               FStar_Tactics_Types.local_state =
                 (ps.FStar_Tactics_Types.local_state);
               FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
             } in
           do_dump_ps msg ps'; FStar_Tactics_Result.Success ((), ps))
let fail1 :
  'uuuuu . Prims.string -> Prims.string -> 'uuuuu FStar_Tactics_Monad.tac =
  fun msg ->
    fun x ->
      let uu___ = FStar_Compiler_Util.format1 msg x in
      FStar_Tactics_Monad.fail uu___
let fail2 :
  'uuuuu .
    Prims.string ->
      Prims.string -> Prims.string -> 'uuuuu FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        let uu___ = FStar_Compiler_Util.format2 msg x y in
        FStar_Tactics_Monad.fail uu___
let fail3 :
  'uuuuu .
    Prims.string ->
      Prims.string ->
        Prims.string -> Prims.string -> 'uuuuu FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          let uu___ = FStar_Compiler_Util.format3 msg x y z in
          FStar_Tactics_Monad.fail uu___
let fail4 :
  'uuuuu .
    Prims.string ->
      Prims.string ->
        Prims.string ->
          Prims.string -> Prims.string -> 'uuuuu FStar_Tactics_Monad.tac
  =
  fun msg ->
    fun x ->
      fun y ->
        fun z ->
          fun w ->
            let uu___ = FStar_Compiler_Util.format4 msg x y z w in
            FStar_Tactics_Monad.fail uu___
let (destruct_eq' :
  FStar_Syntax_Syntax.typ ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun typ ->
    let uu___ = FStar_Syntax_Util.destruct_typ_as_formula typ in
    match uu___ with
    | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn
        (l,
         uu___1::(e1, FStar_Pervasives_Native.None)::(e2,
                                                      FStar_Pervasives_Native.None)::[]))
        when
        (FStar_Ident.lid_equals l FStar_Parser_Const.eq2_lid) ||
          (FStar_Ident.lid_equals l FStar_Parser_Const.c_eq2_lid)
        -> FStar_Pervasives_Native.Some (e1, e2)
    | uu___1 ->
        let uu___2 = FStar_Syntax_Util.unb2t typ in
        (match uu___2 with
         | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
         | FStar_Pervasives_Native.Some t ->
             let uu___3 = FStar_Syntax_Util.head_and_args t in
             (match uu___3 with
              | (hd, args) ->
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStar_Syntax_Subst.compress hd in
                      uu___6.FStar_Syntax_Syntax.n in
                    (uu___5, args) in
                  (match uu___4 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,
                      (uu___5, FStar_Pervasives_Native.Some
                       { FStar_Syntax_Syntax.aqual_implicit = true;
                         FStar_Syntax_Syntax.aqual_attributes = uu___6;_})::
                      (e1, FStar_Pervasives_Native.None)::(e2,
                                                           FStar_Pervasives_Native.None)::[])
                       when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.op_Eq
                       -> FStar_Pervasives_Native.Some (e1, e2)
                   | uu___5 -> FStar_Pervasives_Native.None)))
let (destruct_eq :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.typ ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
        FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun typ ->
      let typ1 = whnf env1 typ in
      let uu___ = destruct_eq' typ1 in
      match uu___ with
      | FStar_Pervasives_Native.Some t -> FStar_Pervasives_Native.Some t
      | FStar_Pervasives_Native.None ->
          let uu___1 = FStar_Syntax_Util.un_squash typ1 in
          (match uu___1 with
           | FStar_Pervasives_Native.Some typ2 ->
               let typ3 = whnf env1 typ2 in destruct_eq' typ3
           | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None)
let (get_guard_policy :
  unit -> FStar_Tactics_Types.guard_policy FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps -> FStar_Tactics_Monad.ret ps.FStar_Tactics_Types.guard_policy)
let (set_guard_policy :
  FStar_Tactics_Types.guard_policy -> unit FStar_Tactics_Monad.tac) =
  fun pol ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Tactics_Monad.set
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (ps.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy = pol;
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
           })
let with_policy :
  'a .
    FStar_Tactics_Types.guard_policy ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun pol ->
    fun t ->
      let uu___ = get_guard_policy () in
      FStar_Tactics_Monad.bind uu___
        (fun old_pol ->
           let uu___1 = set_guard_policy pol in
           FStar_Tactics_Monad.bind uu___1
             (fun uu___2 ->
                FStar_Tactics_Monad.bind t
                  (fun r ->
                     let uu___3 = set_guard_policy old_pol in
                     FStar_Tactics_Monad.bind uu___3
                       (fun uu___4 -> FStar_Tactics_Monad.ret r))))
let (proc_guard' :
  Prims.bool ->
    Prims.string ->
      env ->
        FStar_TypeChecker_Common.guard_t ->
          FStar_Syntax_Syntax.should_check_uvar
            FStar_Pervasives_Native.option ->
            FStar_Compiler_Range_Type.range -> unit FStar_Tactics_Monad.tac)
  =
  fun simplify ->
    fun reason ->
      fun e ->
        fun g ->
          fun sc_opt ->
            fun rng ->
              FStar_Tactics_Monad.mlog
                (fun uu___ ->
                   let uu___1 = FStar_TypeChecker_Rel.guard_to_string e g in
                   FStar_Compiler_Util.print2 "Processing guard (%s:%s)\n"
                     reason uu___1)
                (fun uu___ ->
                   (match sc_opt with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Allow_untyped r) ->
                        FStar_Compiler_List.iter
                          (fun imp ->
                             mark_uvar_with_should_check_tag
                               imp.FStar_TypeChecker_Common.imp_uvar
                               (FStar_Syntax_Syntax.Allow_untyped r))
                          g.FStar_TypeChecker_Common.implicits
                    | uu___2 -> ());
                   (let uu___2 =
                      FStar_Tactics_Monad.add_implicits
                        g.FStar_TypeChecker_Common.implicits in
                    FStar_Tactics_Monad.op_let_Bang uu___2
                      (fun uu___3 ->
                         let guard_f =
                           if simplify
                           then
                             let uu___4 =
                               FStar_TypeChecker_Rel.simplify_guard e g in
                             uu___4.FStar_TypeChecker_Common.guard_f
                           else g.FStar_TypeChecker_Common.guard_f in
                         match guard_f with
                         | FStar_TypeChecker_Common.Trivial ->
                             FStar_Tactics_Monad.ret ()
                         | FStar_TypeChecker_Common.NonTrivial f ->
                             FStar_Tactics_Monad.op_let_Bang
                               FStar_Tactics_Monad.get
                               (fun ps ->
                                  match ps.FStar_Tactics_Types.guard_policy
                                  with
                                  | FStar_Tactics_Types.Drop ->
                                      ((let uu___5 =
                                          let uu___6 =
                                            let uu___7 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e g in
                                            FStar_Compiler_Util.format1
                                              "Tactics admitted guard <%s>\n\n"
                                              uu___7 in
                                          (FStar_Errors_Codes.Warning_TacAdmit,
                                            uu___6) in
                                        FStar_Errors.log_issue
                                          e.FStar_TypeChecker_Env.range
                                          uu___5);
                                       FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Goal ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu___4 ->
                                           let uu___5 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Compiler_Util.print2
                                             "Making guard (%s:%s) into a goal\n"
                                             reason uu___5)
                                        (fun uu___4 ->
                                           let uu___5 =
                                             FStar_Tactics_Monad.goal_of_guard
                                               reason e f sc_opt rng in
                                           FStar_Tactics_Monad.op_let_Bang
                                             uu___5
                                             (fun g1 ->
                                                FStar_Tactics_Monad.push_goals
                                                  [g1]))
                                  | FStar_Tactics_Types.SMT ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu___4 ->
                                           let uu___5 =
                                             FStar_Syntax_Print.term_to_string
                                               f in
                                           FStar_Compiler_Util.print2
                                             "Pushing guard (%s:%s) as SMT goal\n"
                                             reason uu___5)
                                        (fun uu___4 ->
                                           let uu___5 =
                                             FStar_Tactics_Monad.goal_of_guard
                                               reason e f sc_opt rng in
                                           FStar_Tactics_Monad.op_let_Bang
                                             uu___5
                                             (fun g1 ->
                                                FStar_Tactics_Monad.push_smt_goals
                                                  [g1]))
                                  | FStar_Tactics_Types.SMTSync ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu___4 ->
                                           let uu___5 =
                                             FStar_Syntax_Print.term_to_string
                                               f in
                                           FStar_Compiler_Util.print2
                                             "Sending guard (%s:%s) to SMT Synchronously\n"
                                             reason uu___5)
                                        (fun uu___4 ->
                                           FStar_TypeChecker_Rel.force_trivial_guard
                                             e g;
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Tactics_Types.Force ->
                                      FStar_Tactics_Monad.mlog
                                        (fun uu___4 ->
                                           let uu___5 =
                                             FStar_TypeChecker_Rel.guard_to_string
                                               e g in
                                           FStar_Compiler_Util.print2
                                             "Forcing guard (%s:%s)\n" reason
                                             uu___5)
                                        (fun uu___4 ->
                                           try
                                             (fun uu___5 ->
                                                match () with
                                                | () ->
                                                    let uu___6 =
                                                      let uu___7 =
                                                        let uu___8 =
                                                          FStar_TypeChecker_Rel.discharge_guard_no_smt
                                                            e g in
                                                        FStar_Compiler_Effect.op_Less_Bar
                                                          FStar_TypeChecker_Env.is_trivial
                                                          uu___8 in
                                                      Prims.op_Negation
                                                        uu___7 in
                                                    if uu___6
                                                    then
                                                      FStar_Tactics_Monad.mlog
                                                        (fun uu___7 ->
                                                           let uu___8 =
                                                             FStar_TypeChecker_Rel.guard_to_string
                                                               e g in
                                                           FStar_Compiler_Util.print1
                                                             "guard = %s\n"
                                                             uu___8)
                                                        (fun uu___7 ->
                                                           fail1
                                                             "Forcing the guard failed (%s)"
                                                             reason)
                                                    else
                                                      FStar_Tactics_Monad.ret
                                                        ()) ()
                                           with
                                           | uu___5 ->
                                               FStar_Tactics_Monad.mlog
                                                 (fun uu___6 ->
                                                    let uu___7 =
                                                      FStar_TypeChecker_Rel.guard_to_string
                                                        e g in
                                                    FStar_Compiler_Util.print1
                                                      "guard = %s\n" uu___7)
                                                 (fun uu___6 ->
                                                    fail1
                                                      "Forcing the guard failed (%s)"
                                                      reason))))))
let (proc_guard :
  Prims.string ->
    env ->
      FStar_TypeChecker_Common.guard_t ->
        FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option
          -> FStar_Compiler_Range_Type.range -> unit FStar_Tactics_Monad.tac)
  = proc_guard' true
let (tc_unifier_solved_implicits :
  FStar_TypeChecker_Env.env ->
    Prims.bool ->
      Prims.bool ->
        FStar_Syntax_Syntax.ctx_uvar Prims.list ->
          unit FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun must_tot ->
      fun allow_guards ->
        fun uvs ->
          let aux u =
            let dec =
              FStar_Syntax_Unionfind.find_decoration
                u.FStar_Syntax_Syntax.ctx_uvar_head in
            let sc = dec.FStar_Syntax_Syntax.uvar_decoration_should_check in
            match sc with
            | FStar_Syntax_Syntax.Allow_untyped uu___ ->
                FStar_Tactics_Monad.ret ()
            | FStar_Syntax_Syntax.Already_checked ->
                FStar_Tactics_Monad.ret ()
            | uu___ ->
                let uu___1 =
                  FStar_Syntax_Unionfind.find
                    u.FStar_Syntax_Syntax.ctx_uvar_head in
                (match uu___1 with
                 | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret ()
                 | FStar_Pervasives_Native.Some sol ->
                     let env2 =
                       {
                         FStar_TypeChecker_Env.solver =
                           (env1.FStar_TypeChecker_Env.solver);
                         FStar_TypeChecker_Env.range =
                           (env1.FStar_TypeChecker_Env.range);
                         FStar_TypeChecker_Env.curmodule =
                           (env1.FStar_TypeChecker_Env.curmodule);
                         FStar_TypeChecker_Env.gamma =
                           (u.FStar_Syntax_Syntax.ctx_uvar_gamma);
                         FStar_TypeChecker_Env.gamma_sig =
                           (env1.FStar_TypeChecker_Env.gamma_sig);
                         FStar_TypeChecker_Env.gamma_cache =
                           (env1.FStar_TypeChecker_Env.gamma_cache);
                         FStar_TypeChecker_Env.modules =
                           (env1.FStar_TypeChecker_Env.modules);
                         FStar_TypeChecker_Env.expected_typ =
                           (env1.FStar_TypeChecker_Env.expected_typ);
                         FStar_TypeChecker_Env.sigtab =
                           (env1.FStar_TypeChecker_Env.sigtab);
                         FStar_TypeChecker_Env.attrtab =
                           (env1.FStar_TypeChecker_Env.attrtab);
                         FStar_TypeChecker_Env.instantiate_imp =
                           (env1.FStar_TypeChecker_Env.instantiate_imp);
                         FStar_TypeChecker_Env.effects =
                           (env1.FStar_TypeChecker_Env.effects);
                         FStar_TypeChecker_Env.generalize =
                           (env1.FStar_TypeChecker_Env.generalize);
                         FStar_TypeChecker_Env.letrecs =
                           (env1.FStar_TypeChecker_Env.letrecs);
                         FStar_TypeChecker_Env.top_level =
                           (env1.FStar_TypeChecker_Env.top_level);
                         FStar_TypeChecker_Env.check_uvars =
                           (env1.FStar_TypeChecker_Env.check_uvars);
                         FStar_TypeChecker_Env.use_eq_strict =
                           (env1.FStar_TypeChecker_Env.use_eq_strict);
                         FStar_TypeChecker_Env.is_iface =
                           (env1.FStar_TypeChecker_Env.is_iface);
                         FStar_TypeChecker_Env.admit =
                           (env1.FStar_TypeChecker_Env.admit);
                         FStar_TypeChecker_Env.lax =
                           (env1.FStar_TypeChecker_Env.lax);
                         FStar_TypeChecker_Env.lax_universes =
                           (env1.FStar_TypeChecker_Env.lax_universes);
                         FStar_TypeChecker_Env.phase1 =
                           (env1.FStar_TypeChecker_Env.phase1);
                         FStar_TypeChecker_Env.failhard =
                           (env1.FStar_TypeChecker_Env.failhard);
                         FStar_TypeChecker_Env.nosynth =
                           (env1.FStar_TypeChecker_Env.nosynth);
                         FStar_TypeChecker_Env.uvar_subtyping =
                           (env1.FStar_TypeChecker_Env.uvar_subtyping);
                         FStar_TypeChecker_Env.intactics =
                           (env1.FStar_TypeChecker_Env.intactics);
                         FStar_TypeChecker_Env.nocoerce =
                           (env1.FStar_TypeChecker_Env.nocoerce);
                         FStar_TypeChecker_Env.tc_term =
                           (env1.FStar_TypeChecker_Env.tc_term);
                         FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                           (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                         FStar_TypeChecker_Env.universe_of =
                           (env1.FStar_TypeChecker_Env.universe_of);
                         FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                           =
                           (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                         FStar_TypeChecker_Env.teq_nosmt_force =
                           (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                         FStar_TypeChecker_Env.subtype_nosmt_force =
                           (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                         FStar_TypeChecker_Env.qtbl_name_and_index =
                           (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                         FStar_TypeChecker_Env.normalized_eff_names =
                           (env1.FStar_TypeChecker_Env.normalized_eff_names);
                         FStar_TypeChecker_Env.fv_delta_depths =
                           (env1.FStar_TypeChecker_Env.fv_delta_depths);
                         FStar_TypeChecker_Env.proof_ns =
                           (env1.FStar_TypeChecker_Env.proof_ns);
                         FStar_TypeChecker_Env.synth_hook =
                           (env1.FStar_TypeChecker_Env.synth_hook);
                         FStar_TypeChecker_Env.try_solve_implicits_hook =
                           (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                         FStar_TypeChecker_Env.splice =
                           (env1.FStar_TypeChecker_Env.splice);
                         FStar_TypeChecker_Env.mpreprocess =
                           (env1.FStar_TypeChecker_Env.mpreprocess);
                         FStar_TypeChecker_Env.postprocess =
                           (env1.FStar_TypeChecker_Env.postprocess);
                         FStar_TypeChecker_Env.identifier_info =
                           (env1.FStar_TypeChecker_Env.identifier_info);
                         FStar_TypeChecker_Env.tc_hooks =
                           (env1.FStar_TypeChecker_Env.tc_hooks);
                         FStar_TypeChecker_Env.dsenv =
                           (env1.FStar_TypeChecker_Env.dsenv);
                         FStar_TypeChecker_Env.nbe =
                           (env1.FStar_TypeChecker_Env.nbe);
                         FStar_TypeChecker_Env.strict_args_tab =
                           (env1.FStar_TypeChecker_Env.strict_args_tab);
                         FStar_TypeChecker_Env.erasable_types_tab =
                           (env1.FStar_TypeChecker_Env.erasable_types_tab);
                         FStar_TypeChecker_Env.enable_defer_to_tac =
                           (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                         FStar_TypeChecker_Env.unif_allow_ref_guards =
                           (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                         FStar_TypeChecker_Env.erase_erasable_args =
                           (env1.FStar_TypeChecker_Env.erase_erasable_args);
                         FStar_TypeChecker_Env.core_check =
                           (env1.FStar_TypeChecker_Env.core_check)
                       } in
                     let must_tot1 =
                       must_tot &&
                         (Prims.op_Negation
                            (FStar_Syntax_Syntax.uu___is_Allow_ghost
                               dec.FStar_Syntax_Syntax.uvar_decoration_should_check)) in
                     let uu___2 =
                       let uu___3 = FStar_Syntax_Util.ctx_uvar_typ u in
                       core_check env2 sol uu___3 must_tot1 in
                     (match uu___2 with
                      | FStar_Pervasives.Inl (FStar_Pervasives_Native.None)
                          ->
                          (mark_uvar_as_already_checked u;
                           FStar_Tactics_Monad.ret ())
                      | FStar_Pervasives.Inl (FStar_Pervasives_Native.Some g)
                          ->
                          let guard =
                            {
                              FStar_TypeChecker_Common.guard_f =
                                (FStar_TypeChecker_Common.NonTrivial g);
                              FStar_TypeChecker_Common.deferred_to_tac =
                                (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred_to_tac);
                              FStar_TypeChecker_Common.deferred =
                                (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.deferred);
                              FStar_TypeChecker_Common.univ_ineqs =
                                (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.univ_ineqs);
                              FStar_TypeChecker_Common.implicits =
                                (FStar_TypeChecker_Env.trivial_guard.FStar_TypeChecker_Common.implicits)
                            } in
                          let guard1 =
                            FStar_TypeChecker_Rel.simplify_guard env2 guard in
                          let uu___3 =
                            ((FStar_Options.disallow_unification_guards ())
                               && (Prims.op_Negation allow_guards))
                              &&
                              (FStar_TypeChecker_Common.uu___is_NonTrivial
                                 guard1.FStar_TypeChecker_Common.guard_f) in
                          if uu___3
                          then
                            let uu___4 =
                              FStar_Syntax_Print.uvar_to_string
                                u.FStar_Syntax_Syntax.ctx_uvar_head in
                            let uu___5 =
                              FStar_Syntax_Print.term_to_string sol in
                            let uu___6 = FStar_Syntax_Print.term_to_string g in
                            fail3
                              "Could not typecheck unifier solved implicit %s to %s since it produced a guard and guards were not allowed;guard is\n%s"
                              uu___4 uu___5 uu___6
                          else
                            (let uu___5 =
                               proc_guard' false "guard for implicit" env2
                                 guard1 (FStar_Pervasives_Native.Some sc)
                                 u.FStar_Syntax_Syntax.ctx_uvar_range in
                             FStar_Tactics_Monad.op_let_Bang uu___5
                               (fun uu___6 ->
                                  mark_uvar_as_already_checked u;
                                  FStar_Tactics_Monad.ret ()))
                      | FStar_Pervasives.Inr failed ->
                          let uu___3 =
                            FStar_Syntax_Print.uvar_to_string
                              u.FStar_Syntax_Syntax.ctx_uvar_head in
                          let uu___4 = FStar_Syntax_Print.term_to_string sol in
                          let uu___5 =
                            FStar_TypeChecker_Core.print_error failed in
                          fail3
                            "Could not typecheck unifier solved implicit %s to %s because %s"
                            uu___3 uu___4 uu___5)) in
          if env1.FStar_TypeChecker_Env.phase1
          then FStar_Tactics_Monad.ret ()
          else
            FStar_Compiler_Effect.op_Bar_Greater uvs
              (FStar_Tactics_Monad.iter_tac aux)
type check_unifier_solved_implicits_side =
  | Check_none 
  | Check_left_only 
  | Check_right_only 
  | Check_both 
let (uu___is_Check_none : check_unifier_solved_implicits_side -> Prims.bool)
  =
  fun projectee -> match projectee with | Check_none -> true | uu___ -> false
let (uu___is_Check_left_only :
  check_unifier_solved_implicits_side -> Prims.bool) =
  fun projectee ->
    match projectee with | Check_left_only -> true | uu___ -> false
let (uu___is_Check_right_only :
  check_unifier_solved_implicits_side -> Prims.bool) =
  fun projectee ->
    match projectee with | Check_right_only -> true | uu___ -> false
let (uu___is_Check_both : check_unifier_solved_implicits_side -> Prims.bool)
  =
  fun projectee -> match projectee with | Check_both -> true | uu___ -> false
let (__do_unify_wflags :
  Prims.bool ->
    Prims.bool ->
      Prims.bool ->
        check_unifier_solved_implicits_side ->
          env ->
            FStar_Syntax_Syntax.term ->
              FStar_Syntax_Syntax.term ->
                FStar_TypeChecker_Common.guard_t
                  FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun dbg ->
    fun allow_guards ->
      fun must_tot ->
        fun check_side ->
          fun env1 ->
            fun t1 ->
              fun t2 ->
                if dbg
                then
                  (let uu___1 = FStar_Syntax_Print.term_to_string t1 in
                   let uu___2 = FStar_Syntax_Print.term_to_string t2 in
                   FStar_Compiler_Util.print2 "%%%%%%%%do_unify %s =? %s\n"
                     uu___1 uu___2)
                else ();
                (let all_uvars =
                   let uu___1 =
                     match check_side with
                     | Check_none -> FStar_Syntax_Free.new_uv_set ()
                     | Check_left_only -> FStar_Syntax_Free.uvars t1
                     | Check_right_only -> FStar_Syntax_Free.uvars t2
                     | Check_both ->
                         let uu___2 = FStar_Syntax_Free.uvars t1 in
                         let uu___3 = FStar_Syntax_Free.uvars t2 in
                         FStar_Compiler_Util.set_union uu___2 uu___3 in
                   FStar_Compiler_Effect.op_Bar_Greater uu___1
                     FStar_Compiler_Util.set_elements in
                 let uu___1 =
                   let uu___2 =
                     let uu___3 =
                       FStar_Tactics_Monad.trytac
                         FStar_Tactics_Monad.cur_goal in
                     FStar_Tactics_Monad.bind uu___3
                       (fun gopt ->
                          try
                            (fun uu___4 ->
                               match () with
                               | () ->
                                   let res =
                                     if allow_guards
                                     then
                                       FStar_TypeChecker_Rel.try_teq true
                                         env1 t1 t2
                                     else
                                       FStar_TypeChecker_Rel.teq_nosmt env1
                                         t1 t2 in
                                   (if dbg
                                    then
                                      (let uu___6 =
                                         FStar_Common.string_of_option
                                           (FStar_TypeChecker_Rel.guard_to_string
                                              env1) res in
                                       let uu___7 =
                                         FStar_Syntax_Print.term_to_string t1 in
                                       let uu___8 =
                                         FStar_Syntax_Print.term_to_string t2 in
                                       FStar_Compiler_Util.print3
                                         "%%%%%%%%do_unify (RESULT %s) %s =? %s\n"
                                         uu___6 uu___7 uu___8)
                                    else ();
                                    (match res with
                                     | FStar_Pervasives_Native.None ->
                                         FStar_Tactics_Monad.ret
                                           FStar_Pervasives_Native.None
                                     | FStar_Pervasives_Native.Some g ->
                                         let uu___6 =
                                           tc_unifier_solved_implicits env1
                                             must_tot allow_guards all_uvars in
                                         FStar_Tactics_Monad.op_let_Bang
                                           uu___6
                                           (fun uu___7 ->
                                              let uu___8 =
                                                FStar_Tactics_Monad.add_implicits
                                                  g.FStar_TypeChecker_Common.implicits in
                                              FStar_Tactics_Monad.op_let_Bang
                                                uu___8
                                                (fun uu___9 ->
                                                   FStar_Tactics_Monad.ret
                                                     (FStar_Pervasives_Native.Some
                                                        g)))))) ()
                          with
                          | FStar_Errors.Err (uu___5, msg, uu___6) ->
                              FStar_Tactics_Monad.mlog
                                (fun uu___7 ->
                                   let uu___8 =
                                     FStar_Errors_Msg.rendermsg msg in
                                   FStar_Compiler_Util.print1
                                     ">> do_unify error, (%s)\n" uu___8)
                                (fun uu___7 ->
                                   FStar_Tactics_Monad.ret
                                     FStar_Pervasives_Native.None)
                          | FStar_Errors.Error (uu___5, msg, r, uu___6) ->
                              FStar_Tactics_Monad.mlog
                                (fun uu___7 ->
                                   let uu___8 =
                                     FStar_Errors_Msg.rendermsg msg in
                                   let uu___9 =
                                     FStar_Compiler_Range_Ops.string_of_range
                                       r in
                                   FStar_Compiler_Util.print2
                                     ">> do_unify error, (%s) at (%s)\n"
                                     uu___8 uu___9)
                                (fun uu___7 ->
                                   FStar_Tactics_Monad.ret
                                     FStar_Pervasives_Native.None)) in
                   FStar_Tactics_Monad.catch uu___2 in
                 FStar_Tactics_Monad.op_let_Bang uu___1
                   (fun uu___2 ->
                      match uu___2 with
                      | FStar_Pervasives.Inl exn ->
                          FStar_Tactics_Monad.traise exn
                      | FStar_Pervasives.Inr v -> FStar_Tactics_Monad.ret v))
let (__do_unify :
  Prims.bool ->
    Prims.bool ->
      check_unifier_solved_implicits_side ->
        env ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.term ->
              FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
                FStar_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun must_tot ->
      fun check_side ->
        fun env1 ->
          fun t1 ->
            fun t2 ->
              let dbg =
                FStar_TypeChecker_Env.debug env1
                  (FStar_Options.Other "TacUnify") in
              FStar_Tactics_Monad.bind FStar_Tactics_Monad.idtac
                (fun uu___ ->
                   if dbg
                   then
                     (FStar_Options.push ();
                      (let uu___3 =
                         FStar_Options.set_options
                           "--debug_level Rel --debug_level RelCheck" in
                       ()))
                   else ();
                   (let uu___2 =
                      __do_unify_wflags dbg allow_guards must_tot check_side
                        env1 t1 t2 in
                    FStar_Tactics_Monad.bind uu___2
                      (fun r ->
                         if dbg then FStar_Options.pop () else ();
                         FStar_Tactics_Monad.ret r)))
let (do_unify_aux :
  Prims.bool ->
    check_unifier_solved_implicits_side ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun must_tot ->
    fun check_side ->
      fun env1 ->
        fun t1 ->
          fun t2 ->
            let uu___ = __do_unify false must_tot check_side env1 t1 t2 in
            FStar_Tactics_Monad.bind uu___
              (fun uu___1 ->
                 match uu___1 with
                 | FStar_Pervasives_Native.None ->
                     FStar_Tactics_Monad.ret false
                 | FStar_Pervasives_Native.Some g ->
                     ((let uu___3 =
                         let uu___4 =
                           FStar_TypeChecker_Env.is_trivial_guard_formula g in
                         Prims.op_Negation uu___4 in
                       if uu___3
                       then
                         failwith
                           "internal error: do_unify: guard is not trivial"
                       else ());
                      FStar_Tactics_Monad.ret true))
let (do_unify :
  Prims.bool ->
    env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun must_tot ->
    fun env1 ->
      fun t1 -> fun t2 -> do_unify_aux must_tot Check_both env1 t1 t2
let (do_unify_maybe_guards :
  Prims.bool ->
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_TypeChecker_Common.guard_t FStar_Pervasives_Native.option
              FStar_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun must_tot ->
      fun env1 ->
        fun t1 ->
          fun t2 -> __do_unify allow_guards must_tot Check_both env1 t1 t2
let (do_match :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun must_tot ->
    fun env1 ->
      fun t1 ->
        fun t2 ->
          let uu___ =
            FStar_Tactics_Monad.mk_tac
              (fun ps ->
                 let tx = FStar_Syntax_Unionfind.new_transaction () in
                 FStar_Tactics_Result.Success (tx, ps)) in
          FStar_Tactics_Monad.bind uu___
            (fun tx ->
               let uvs1 = FStar_Syntax_Free.uvars_uncached t1 in
               let uu___1 = do_unify_aux must_tot Check_right_only env1 t1 t2 in
               FStar_Tactics_Monad.bind uu___1
                 (fun r ->
                    if r
                    then
                      let uvs2 = FStar_Syntax_Free.uvars_uncached t1 in
                      let uu___2 =
                        let uu___3 = FStar_Compiler_Util.set_eq uvs1 uvs2 in
                        Prims.op_Negation uu___3 in
                      (if uu___2
                       then
                         (FStar_Syntax_Unionfind.rollback tx;
                          FStar_Tactics_Monad.ret false)
                       else FStar_Tactics_Monad.ret true)
                    else FStar_Tactics_Monad.ret false))
let (do_match_on_lhs :
  Prims.bool ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun must_tot ->
    fun env1 ->
      fun t1 ->
        fun t2 ->
          let uu___ =
            FStar_Tactics_Monad.mk_tac
              (fun ps ->
                 let tx = FStar_Syntax_Unionfind.new_transaction () in
                 FStar_Tactics_Result.Success (tx, ps)) in
          FStar_Tactics_Monad.bind uu___
            (fun tx ->
               let uu___1 = destruct_eq env1 t1 in
               match uu___1 with
               | FStar_Pervasives_Native.None ->
                   FStar_Tactics_Monad.fail "do_match_on_lhs: not an eq"
               | FStar_Pervasives_Native.Some (lhs, uu___2) ->
                   let uvs1 = FStar_Syntax_Free.uvars_uncached lhs in
                   let uu___3 =
                     do_unify_aux must_tot Check_right_only env1 t1 t2 in
                   FStar_Tactics_Monad.bind uu___3
                     (fun r ->
                        if r
                        then
                          let uvs2 = FStar_Syntax_Free.uvars_uncached lhs in
                          let uu___4 =
                            let uu___5 = FStar_Compiler_Util.set_eq uvs1 uvs2 in
                            Prims.op_Negation uu___5 in
                          (if uu___4
                           then
                             (FStar_Syntax_Unionfind.rollback tx;
                              FStar_Tactics_Monad.ret false)
                           else FStar_Tactics_Monad.ret true)
                        else FStar_Tactics_Monad.ret false))
let (set_solution :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu___ =
        FStar_Syntax_Unionfind.find
          (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head in
      match uu___ with
      | FStar_Pervasives_Native.Some uu___1 ->
          let uu___2 =
            let uu___3 = FStar_Tactics_Printing.goal_to_string_verbose goal in
            FStar_Compiler_Util.format1 "Goal %s is already solved" uu___3 in
          FStar_Tactics_Monad.fail uu___2
      | FStar_Pervasives_Native.None ->
          (FStar_Syntax_Unionfind.change
             (goal.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_head
             solution;
           mark_goal_implicit_already_checked goal;
           FStar_Tactics_Monad.ret ())
let (trysolve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let must_tot = true in
      let uu___ = FStar_Tactics_Types.goal_env goal in
      let uu___1 = FStar_Tactics_Types.goal_witness goal in
      do_unify must_tot uu___ solution uu___1
let (solve :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let e = FStar_Tactics_Types.goal_env goal in
      FStar_Tactics_Monad.mlog
        (fun uu___ ->
           let uu___1 =
             let uu___2 = FStar_Tactics_Types.goal_witness goal in
             FStar_Syntax_Print.term_to_string uu___2 in
           let uu___2 = FStar_Syntax_Print.term_to_string solution in
           FStar_Compiler_Util.print2 "solve %s := %s\n" uu___1 uu___2)
        (fun uu___ ->
           let uu___1 = trysolve goal solution in
           FStar_Tactics_Monad.bind uu___1
             (fun b ->
                if b
                then
                  FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
                    (fun uu___2 -> FStar_Tactics_Monad.remove_solved_goals)
                else
                  (let uu___3 =
                     let uu___4 =
                       let uu___5 = FStar_Tactics_Types.goal_env goal in
                       tts uu___5 solution in
                     let uu___5 =
                       let uu___6 = FStar_Tactics_Types.goal_env goal in
                       let uu___7 = FStar_Tactics_Types.goal_witness goal in
                       tts uu___6 uu___7 in
                     let uu___6 =
                       let uu___7 = FStar_Tactics_Types.goal_env goal in
                       let uu___8 = FStar_Tactics_Types.goal_type goal in
                       tts uu___7 uu___8 in
                     FStar_Compiler_Util.format3 "%s does not solve %s : %s"
                       uu___4 uu___5 uu___6 in
                   FStar_Tactics_Monad.fail uu___3)))
let (solve' :
  FStar_Tactics_Types.goal ->
    FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun goal ->
    fun solution ->
      let uu___ = set_solution goal solution in
      FStar_Tactics_Monad.bind uu___
        (fun uu___1 ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.dismiss
             (fun uu___2 -> FStar_Tactics_Monad.remove_solved_goals))
let (is_true : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let t1 = FStar_Syntax_Util.unascribe t in
    let uu___ = FStar_Syntax_Util.un_squash t1 in
    match uu___ with
    | FStar_Pervasives_Native.Some t' ->
        let t'1 = FStar_Syntax_Util.unascribe t' in
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t'1 in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.true_lid
         | uu___2 -> false)
    | uu___1 -> false
let (is_false : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    let uu___ = FStar_Syntax_Util.un_squash t in
    match uu___ with
    | FStar_Pervasives_Native.Some t' ->
        let uu___1 =
          let uu___2 = FStar_Syntax_Subst.compress t' in
          uu___2.FStar_Syntax_Syntax.n in
        (match uu___1 with
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.false_lid
         | uu___2 -> false)
    | uu___1 -> false
let (tadmit_t : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu___ =
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.bind FStar_Tactics_Monad.cur_goal
             (fun g ->
                (let uu___2 =
                   let uu___3 = FStar_Tactics_Types.goal_type g in
                   uu___3.FStar_Syntax_Syntax.pos in
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStar_Tactics_Printing.goal_to_string ""
                         FStar_Pervasives_Native.None ps g in
                     FStar_Compiler_Util.format1
                       "Tactics admitted goal <%s>\n\n" uu___5 in
                   (FStar_Errors_Codes.Warning_TacAdmit, uu___4) in
                 FStar_Errors.log_issue uu___2 uu___3);
                solve' g t)) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "tadmit_t") uu___
let (fresh : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         let n = ps.FStar_Tactics_Types.freshness in
         let ps1 =
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (ps.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (ps.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness = (n + Prims.int_one);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = (ps.FStar_Tactics_Types.urgency)
           } in
         let uu___1 = FStar_Tactics_Monad.set ps1 in
         FStar_Tactics_Monad.bind uu___1
           (fun uu___2 ->
              let uu___3 = FStar_BigInt.of_int_fs n in
              FStar_Tactics_Monad.ret uu___3))
let (curms : unit -> FStar_BigInt.t FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_Compiler_Util.now_ms () in
      FStar_Compiler_Effect.op_Bar_Greater uu___2 FStar_BigInt.of_int_fs in
    FStar_Tactics_Monad.ret uu___1
let (__tc :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu___ ->
                let uu___1 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.print1 "Tac> __tc(%s)\n" uu___1)
             (fun uu___ ->
                let e1 =
                  {
                    FStar_TypeChecker_Env.solver =
                      (e.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (e.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (e.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (e.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (e.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (e.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (e.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (e.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (e.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (e.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (e.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (e.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (e.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (e.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (e.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (e.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (e.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (e.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (e.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (e.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.intactics =
                      (e.FStar_TypeChecker_Env.intactics);
                    FStar_TypeChecker_Env.nocoerce =
                      (e.FStar_TypeChecker_Env.nocoerce);
                    FStar_TypeChecker_Env.tc_term =
                      (e.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStar_TypeChecker_Env.universe_of =
                      (e.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStar_TypeChecker_Env.teq_nosmt_force =
                      (e.FStar_TypeChecker_Env.teq_nosmt_force);
                    FStar_TypeChecker_Env.subtype_nosmt_force =
                      (e.FStar_TypeChecker_Env.subtype_nosmt_force);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (e.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (e.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (e.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (e.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (e.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (e.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (e.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (e.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (e.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (e.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (e.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe = (e.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (e.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (e.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (e.FStar_TypeChecker_Env.enable_defer_to_tac);
                    FStar_TypeChecker_Env.unif_allow_ref_guards =
                      (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
                    FStar_TypeChecker_Env.erase_erasable_args =
                      (e.FStar_TypeChecker_Env.erase_erasable_args);
                    FStar_TypeChecker_Env.core_check =
                      (e.FStar_TypeChecker_Env.core_check)
                  } in
                try
                  (fun uu___1 ->
                     match () with
                     | () ->
                         let uu___2 =
                           FStar_TypeChecker_TcTerm.typeof_tot_or_gtot_term
                             e1 t true in
                         FStar_Tactics_Monad.ret uu___2) ()
                with
                | FStar_Errors.Err (uu___2, msg, uu___3) ->
                    let uu___4 = tts e1 t in
                    let uu___5 =
                      let uu___6 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___6
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu___6 = FStar_Errors_Msg.rendermsg msg in
                    fail3 "Cannot type (1) %s in context (%s). Error = (%s)"
                      uu___4 uu___5 uu___6
                | FStar_Errors.Error (uu___2, msg, uu___3, uu___4) ->
                    let uu___5 = tts e1 t in
                    let uu___6 =
                      let uu___7 = FStar_TypeChecker_Env.all_binders e1 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___7
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu___7 = FStar_Errors_Msg.rendermsg msg in
                    fail3 "Cannot type (1) %s in context (%s). Error = (%s)"
                      uu___5 uu___6 uu___7))
let (__tc_ghost :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu___ ->
                let uu___1 = FStar_Syntax_Print.term_to_string t in
                FStar_Compiler_Util.print1 "Tac> __tc_ghost(%s)\n" uu___1)
             (fun uu___ ->
                let e1 =
                  {
                    FStar_TypeChecker_Env.solver =
                      (e.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (e.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (e.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (e.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (e.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (e.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (e.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (e.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (e.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (e.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (e.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (e.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (e.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (e.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (e.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (e.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (e.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (e.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (e.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (e.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.intactics =
                      (e.FStar_TypeChecker_Env.intactics);
                    FStar_TypeChecker_Env.nocoerce =
                      (e.FStar_TypeChecker_Env.nocoerce);
                    FStar_TypeChecker_Env.tc_term =
                      (e.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStar_TypeChecker_Env.universe_of =
                      (e.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStar_TypeChecker_Env.teq_nosmt_force =
                      (e.FStar_TypeChecker_Env.teq_nosmt_force);
                    FStar_TypeChecker_Env.subtype_nosmt_force =
                      (e.FStar_TypeChecker_Env.subtype_nosmt_force);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (e.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (e.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (e.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (e.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (e.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (e.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (e.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (e.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (e.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (e.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (e.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe = (e.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (e.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (e.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (e.FStar_TypeChecker_Env.enable_defer_to_tac);
                    FStar_TypeChecker_Env.unif_allow_ref_guards =
                      (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
                    FStar_TypeChecker_Env.erase_erasable_args =
                      (e.FStar_TypeChecker_Env.erase_erasable_args);
                    FStar_TypeChecker_Env.core_check =
                      (e.FStar_TypeChecker_Env.core_check)
                  } in
                let e2 =
                  {
                    FStar_TypeChecker_Env.solver =
                      (e1.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (e1.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (e1.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (e1.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (e1.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (e1.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (e1.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (e1.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (e1.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (e1.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (e1.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (e1.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (e1.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs = [];
                    FStar_TypeChecker_Env.top_level =
                      (e1.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (e1.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (e1.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (e1.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (e1.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (e1.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (e1.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e1.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e1.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e1.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (e1.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.intactics =
                      (e1.FStar_TypeChecker_Env.intactics);
                    FStar_TypeChecker_Env.nocoerce =
                      (e1.FStar_TypeChecker_Env.nocoerce);
                    FStar_TypeChecker_Env.tc_term =
                      (e1.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStar_TypeChecker_Env.universe_of =
                      (e1.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStar_TypeChecker_Env.teq_nosmt_force =
                      (e1.FStar_TypeChecker_Env.teq_nosmt_force);
                    FStar_TypeChecker_Env.subtype_nosmt_force =
                      (e1.FStar_TypeChecker_Env.subtype_nosmt_force);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (e1.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (e1.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (e1.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (e1.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (e1.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (e1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (e1.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (e1.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (e1.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (e1.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (e1.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (e1.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (e1.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (e1.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (e1.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (e1.FStar_TypeChecker_Env.enable_defer_to_tac);
                    FStar_TypeChecker_Env.unif_allow_ref_guards =
                      (e1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                    FStar_TypeChecker_Env.erase_erasable_args =
                      (e1.FStar_TypeChecker_Env.erase_erasable_args);
                    FStar_TypeChecker_Env.core_check =
                      (e1.FStar_TypeChecker_Env.core_check)
                  } in
                try
                  (fun uu___1 ->
                     match () with
                     | () ->
                         let uu___2 =
                           FStar_TypeChecker_TcTerm.tc_tot_or_gtot_term e2 t in
                         (match uu___2 with
                          | (t1, lc, g) ->
                              FStar_Tactics_Monad.ret
                                (t1, (lc.FStar_TypeChecker_Common.res_typ),
                                  g))) ()
                with
                | FStar_Errors.Err (uu___2, msg, uu___3) ->
                    let uu___4 = tts e2 t in
                    let uu___5 =
                      let uu___6 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___6
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu___6 = FStar_Errors_Msg.rendermsg msg in
                    fail3 "Cannot type (2) %s in context (%s). Error = (%s)"
                      uu___4 uu___5 uu___6
                | FStar_Errors.Error (uu___2, msg, uu___3, uu___4) ->
                    let uu___5 = tts e2 t in
                    let uu___6 =
                      let uu___7 = FStar_TypeChecker_Env.all_binders e2 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___7
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu___7 = FStar_Errors_Msg.rendermsg msg in
                    fail3 "Cannot type (2) %s in context (%s). Error = (%s)"
                      uu___5 uu___6 uu___7))
let (__tc_lax :
  env ->
    FStar_Syntax_Syntax.term ->
      (FStar_Syntax_Syntax.term * FStar_TypeChecker_Common.lcomp *
        FStar_TypeChecker_Common.guard_t) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
        (fun ps ->
           FStar_Tactics_Monad.mlog
             (fun uu___ ->
                let uu___1 = FStar_Syntax_Print.term_to_string t in
                let uu___2 =
                  let uu___3 = FStar_TypeChecker_Env.all_binders e in
                  FStar_Compiler_Effect.op_Bar_Greater uu___3
                    (FStar_Syntax_Print.binders_to_string ", ") in
                FStar_Compiler_Util.print2 "Tac> __tc_lax(%s)(Context:%s)\n"
                  uu___1 uu___2)
             (fun uu___ ->
                let e1 =
                  {
                    FStar_TypeChecker_Env.solver =
                      (e.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (e.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (e.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (e.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (e.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (e.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (e.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (e.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (e.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (e.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (e.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (e.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (e.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (e.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (e.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (e.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (e.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (e.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (e.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (e.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping = false;
                    FStar_TypeChecker_Env.intactics =
                      (e.FStar_TypeChecker_Env.intactics);
                    FStar_TypeChecker_Env.nocoerce =
                      (e.FStar_TypeChecker_Env.nocoerce);
                    FStar_TypeChecker_Env.tc_term =
                      (e.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStar_TypeChecker_Env.universe_of =
                      (e.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStar_TypeChecker_Env.teq_nosmt_force =
                      (e.FStar_TypeChecker_Env.teq_nosmt_force);
                    FStar_TypeChecker_Env.subtype_nosmt_force =
                      (e.FStar_TypeChecker_Env.subtype_nosmt_force);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (e.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (e.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (e.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (e.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (e.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (e.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (e.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (e.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (e.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (e.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (e.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe = (e.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (e.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (e.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (e.FStar_TypeChecker_Env.enable_defer_to_tac);
                    FStar_TypeChecker_Env.unif_allow_ref_guards =
                      (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
                    FStar_TypeChecker_Env.erase_erasable_args =
                      (e.FStar_TypeChecker_Env.erase_erasable_args);
                    FStar_TypeChecker_Env.core_check =
                      (e.FStar_TypeChecker_Env.core_check)
                  } in
                let e2 =
                  {
                    FStar_TypeChecker_Env.solver =
                      (e1.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (e1.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (e1.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (e1.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (e1.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (e1.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (e1.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (e1.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (e1.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (e1.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (e1.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (e1.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (e1.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs =
                      (e1.FStar_TypeChecker_Env.letrecs);
                    FStar_TypeChecker_Env.top_level =
                      (e1.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (e1.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (e1.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (e1.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (e1.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax = true;
                    FStar_TypeChecker_Env.lax_universes =
                      (e1.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e1.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e1.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e1.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (e1.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.intactics =
                      (e1.FStar_TypeChecker_Env.intactics);
                    FStar_TypeChecker_Env.nocoerce =
                      (e1.FStar_TypeChecker_Env.nocoerce);
                    FStar_TypeChecker_Env.tc_term =
                      (e1.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStar_TypeChecker_Env.universe_of =
                      (e1.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStar_TypeChecker_Env.teq_nosmt_force =
                      (e1.FStar_TypeChecker_Env.teq_nosmt_force);
                    FStar_TypeChecker_Env.subtype_nosmt_force =
                      (e1.FStar_TypeChecker_Env.subtype_nosmt_force);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (e1.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (e1.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (e1.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (e1.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (e1.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (e1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (e1.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (e1.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (e1.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (e1.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (e1.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (e1.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (e1.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (e1.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (e1.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (e1.FStar_TypeChecker_Env.enable_defer_to_tac);
                    FStar_TypeChecker_Env.unif_allow_ref_guards =
                      (e1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                    FStar_TypeChecker_Env.erase_erasable_args =
                      (e1.FStar_TypeChecker_Env.erase_erasable_args);
                    FStar_TypeChecker_Env.core_check =
                      (e1.FStar_TypeChecker_Env.core_check)
                  } in
                let e3 =
                  {
                    FStar_TypeChecker_Env.solver =
                      (e2.FStar_TypeChecker_Env.solver);
                    FStar_TypeChecker_Env.range =
                      (e2.FStar_TypeChecker_Env.range);
                    FStar_TypeChecker_Env.curmodule =
                      (e2.FStar_TypeChecker_Env.curmodule);
                    FStar_TypeChecker_Env.gamma =
                      (e2.FStar_TypeChecker_Env.gamma);
                    FStar_TypeChecker_Env.gamma_sig =
                      (e2.FStar_TypeChecker_Env.gamma_sig);
                    FStar_TypeChecker_Env.gamma_cache =
                      (e2.FStar_TypeChecker_Env.gamma_cache);
                    FStar_TypeChecker_Env.modules =
                      (e2.FStar_TypeChecker_Env.modules);
                    FStar_TypeChecker_Env.expected_typ =
                      (e2.FStar_TypeChecker_Env.expected_typ);
                    FStar_TypeChecker_Env.sigtab =
                      (e2.FStar_TypeChecker_Env.sigtab);
                    FStar_TypeChecker_Env.attrtab =
                      (e2.FStar_TypeChecker_Env.attrtab);
                    FStar_TypeChecker_Env.instantiate_imp =
                      (e2.FStar_TypeChecker_Env.instantiate_imp);
                    FStar_TypeChecker_Env.effects =
                      (e2.FStar_TypeChecker_Env.effects);
                    FStar_TypeChecker_Env.generalize =
                      (e2.FStar_TypeChecker_Env.generalize);
                    FStar_TypeChecker_Env.letrecs = [];
                    FStar_TypeChecker_Env.top_level =
                      (e2.FStar_TypeChecker_Env.top_level);
                    FStar_TypeChecker_Env.check_uvars =
                      (e2.FStar_TypeChecker_Env.check_uvars);
                    FStar_TypeChecker_Env.use_eq_strict =
                      (e2.FStar_TypeChecker_Env.use_eq_strict);
                    FStar_TypeChecker_Env.is_iface =
                      (e2.FStar_TypeChecker_Env.is_iface);
                    FStar_TypeChecker_Env.admit =
                      (e2.FStar_TypeChecker_Env.admit);
                    FStar_TypeChecker_Env.lax =
                      (e2.FStar_TypeChecker_Env.lax);
                    FStar_TypeChecker_Env.lax_universes =
                      (e2.FStar_TypeChecker_Env.lax_universes);
                    FStar_TypeChecker_Env.phase1 =
                      (e2.FStar_TypeChecker_Env.phase1);
                    FStar_TypeChecker_Env.failhard =
                      (e2.FStar_TypeChecker_Env.failhard);
                    FStar_TypeChecker_Env.nosynth =
                      (e2.FStar_TypeChecker_Env.nosynth);
                    FStar_TypeChecker_Env.uvar_subtyping =
                      (e2.FStar_TypeChecker_Env.uvar_subtyping);
                    FStar_TypeChecker_Env.intactics =
                      (e2.FStar_TypeChecker_Env.intactics);
                    FStar_TypeChecker_Env.nocoerce =
                      (e2.FStar_TypeChecker_Env.nocoerce);
                    FStar_TypeChecker_Env.tc_term =
                      (e2.FStar_TypeChecker_Env.tc_term);
                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                      (e2.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                    FStar_TypeChecker_Env.universe_of =
                      (e2.FStar_TypeChecker_Env.universe_of);
                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                      =
                      (e2.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                    FStar_TypeChecker_Env.teq_nosmt_force =
                      (e2.FStar_TypeChecker_Env.teq_nosmt_force);
                    FStar_TypeChecker_Env.subtype_nosmt_force =
                      (e2.FStar_TypeChecker_Env.subtype_nosmt_force);
                    FStar_TypeChecker_Env.qtbl_name_and_index =
                      (e2.FStar_TypeChecker_Env.qtbl_name_and_index);
                    FStar_TypeChecker_Env.normalized_eff_names =
                      (e2.FStar_TypeChecker_Env.normalized_eff_names);
                    FStar_TypeChecker_Env.fv_delta_depths =
                      (e2.FStar_TypeChecker_Env.fv_delta_depths);
                    FStar_TypeChecker_Env.proof_ns =
                      (e2.FStar_TypeChecker_Env.proof_ns);
                    FStar_TypeChecker_Env.synth_hook =
                      (e2.FStar_TypeChecker_Env.synth_hook);
                    FStar_TypeChecker_Env.try_solve_implicits_hook =
                      (e2.FStar_TypeChecker_Env.try_solve_implicits_hook);
                    FStar_TypeChecker_Env.splice =
                      (e2.FStar_TypeChecker_Env.splice);
                    FStar_TypeChecker_Env.mpreprocess =
                      (e2.FStar_TypeChecker_Env.mpreprocess);
                    FStar_TypeChecker_Env.postprocess =
                      (e2.FStar_TypeChecker_Env.postprocess);
                    FStar_TypeChecker_Env.identifier_info =
                      (e2.FStar_TypeChecker_Env.identifier_info);
                    FStar_TypeChecker_Env.tc_hooks =
                      (e2.FStar_TypeChecker_Env.tc_hooks);
                    FStar_TypeChecker_Env.dsenv =
                      (e2.FStar_TypeChecker_Env.dsenv);
                    FStar_TypeChecker_Env.nbe =
                      (e2.FStar_TypeChecker_Env.nbe);
                    FStar_TypeChecker_Env.strict_args_tab =
                      (e2.FStar_TypeChecker_Env.strict_args_tab);
                    FStar_TypeChecker_Env.erasable_types_tab =
                      (e2.FStar_TypeChecker_Env.erasable_types_tab);
                    FStar_TypeChecker_Env.enable_defer_to_tac =
                      (e2.FStar_TypeChecker_Env.enable_defer_to_tac);
                    FStar_TypeChecker_Env.unif_allow_ref_guards =
                      (e2.FStar_TypeChecker_Env.unif_allow_ref_guards);
                    FStar_TypeChecker_Env.erase_erasable_args =
                      (e2.FStar_TypeChecker_Env.erase_erasable_args);
                    FStar_TypeChecker_Env.core_check =
                      (e2.FStar_TypeChecker_Env.core_check)
                  } in
                try
                  (fun uu___1 ->
                     match () with
                     | () ->
                         let uu___2 = FStar_TypeChecker_TcTerm.tc_term e3 t in
                         FStar_Tactics_Monad.ret uu___2) ()
                with
                | FStar_Errors.Err (uu___2, msg, uu___3) ->
                    let uu___4 = tts e3 t in
                    let uu___5 =
                      let uu___6 = FStar_TypeChecker_Env.all_binders e3 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___6
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu___6 = FStar_Errors_Msg.rendermsg msg in
                    fail3 "Cannot type (3) %s in context (%s). Error = (%s)"
                      uu___4 uu___5 uu___6
                | FStar_Errors.Error (uu___2, msg, uu___3, uu___4) ->
                    let uu___5 = tts e3 t in
                    let uu___6 =
                      let uu___7 = FStar_TypeChecker_Env.all_binders e3 in
                      FStar_Compiler_Effect.op_Bar_Greater uu___7
                        (FStar_Syntax_Print.binders_to_string ", ") in
                    let uu___7 = FStar_Errors_Msg.rendermsg msg in
                    fail3 "Cannot type (3) %s in context (%s). Error = (%s)"
                      uu___5 uu___6 uu___7))
let (tcc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.comp FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ =
        let uu___1 = __tc_lax e t in
        FStar_Tactics_Monad.bind uu___1
          (fun uu___2 ->
             match uu___2 with
             | (uu___3, lc, uu___4) ->
                 let uu___5 =
                   let uu___6 = FStar_TypeChecker_Common.lcomp_comp lc in
                   FStar_Compiler_Effect.op_Bar_Greater uu___6
                     FStar_Pervasives_Native.fst in
                 FStar_Tactics_Monad.ret uu___5) in
      FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "tcc")
        uu___
let (tc :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.typ FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t ->
      let uu___ =
        let uu___1 = tcc e t in
        FStar_Tactics_Monad.bind uu___1
          (fun c -> FStar_Tactics_Monad.ret (FStar_Syntax_Util.comp_result c)) in
      FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "tc")
        uu___
let divide :
  'a 'b .
    FStar_BigInt.t ->
      'a FStar_Tactics_Monad.tac ->
        'b FStar_Tactics_Monad.tac -> ('a * 'b) FStar_Tactics_Monad.tac
  =
  fun n ->
    fun l ->
      fun r ->
        FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
          (fun p ->
             let uu___ =
               try
                 (fun uu___1 ->
                    match () with
                    | () ->
                        let uu___2 =
                          let uu___3 = FStar_BigInt.to_int_fs n in
                          FStar_Compiler_List.splitAt uu___3
                            p.FStar_Tactics_Types.goals in
                        FStar_Tactics_Monad.ret uu___2) ()
               with
               | uu___1 ->
                   FStar_Tactics_Monad.fail "divide: not enough goals" in
             FStar_Tactics_Monad.bind uu___
               (fun uu___1 ->
                  match uu___1 with
                  | (lgs, rgs) ->
                      let lp =
                        {
                          FStar_Tactics_Types.main_context =
                            (p.FStar_Tactics_Types.main_context);
                          FStar_Tactics_Types.all_implicits =
                            (p.FStar_Tactics_Types.all_implicits);
                          FStar_Tactics_Types.goals = lgs;
                          FStar_Tactics_Types.smt_goals = [];
                          FStar_Tactics_Types.depth =
                            (p.FStar_Tactics_Types.depth);
                          FStar_Tactics_Types.__dump =
                            (p.FStar_Tactics_Types.__dump);
                          FStar_Tactics_Types.psc =
                            (p.FStar_Tactics_Types.psc);
                          FStar_Tactics_Types.entry_range =
                            (p.FStar_Tactics_Types.entry_range);
                          FStar_Tactics_Types.guard_policy =
                            (p.FStar_Tactics_Types.guard_policy);
                          FStar_Tactics_Types.freshness =
                            (p.FStar_Tactics_Types.freshness);
                          FStar_Tactics_Types.tac_verb_dbg =
                            (p.FStar_Tactics_Types.tac_verb_dbg);
                          FStar_Tactics_Types.local_state =
                            (p.FStar_Tactics_Types.local_state);
                          FStar_Tactics_Types.urgency =
                            (p.FStar_Tactics_Types.urgency)
                        } in
                      let uu___2 = FStar_Tactics_Monad.set lp in
                      FStar_Tactics_Monad.bind uu___2
                        (fun uu___3 ->
                           FStar_Tactics_Monad.bind l
                             (fun a1 ->
                                FStar_Tactics_Monad.bind
                                  FStar_Tactics_Monad.get
                                  (fun lp' ->
                                     let rp =
                                       {
                                         FStar_Tactics_Types.main_context =
                                           (lp'.FStar_Tactics_Types.main_context);
                                         FStar_Tactics_Types.all_implicits =
                                           (lp'.FStar_Tactics_Types.all_implicits);
                                         FStar_Tactics_Types.goals = rgs;
                                         FStar_Tactics_Types.smt_goals = [];
                                         FStar_Tactics_Types.depth =
                                           (lp'.FStar_Tactics_Types.depth);
                                         FStar_Tactics_Types.__dump =
                                           (lp'.FStar_Tactics_Types.__dump);
                                         FStar_Tactics_Types.psc =
                                           (lp'.FStar_Tactics_Types.psc);
                                         FStar_Tactics_Types.entry_range =
                                           (lp'.FStar_Tactics_Types.entry_range);
                                         FStar_Tactics_Types.guard_policy =
                                           (lp'.FStar_Tactics_Types.guard_policy);
                                         FStar_Tactics_Types.freshness =
                                           (lp'.FStar_Tactics_Types.freshness);
                                         FStar_Tactics_Types.tac_verb_dbg =
                                           (lp'.FStar_Tactics_Types.tac_verb_dbg);
                                         FStar_Tactics_Types.local_state =
                                           (lp'.FStar_Tactics_Types.local_state);
                                         FStar_Tactics_Types.urgency =
                                           (lp'.FStar_Tactics_Types.urgency)
                                       } in
                                     let uu___4 = FStar_Tactics_Monad.set rp in
                                     FStar_Tactics_Monad.bind uu___4
                                       (fun uu___5 ->
                                          FStar_Tactics_Monad.bind r
                                            (fun b1 ->
                                               FStar_Tactics_Monad.bind
                                                 FStar_Tactics_Monad.get
                                                 (fun rp' ->
                                                    let p' =
                                                      {
                                                        FStar_Tactics_Types.main_context
                                                          =
                                                          (rp'.FStar_Tactics_Types.main_context);
                                                        FStar_Tactics_Types.all_implicits
                                                          =
                                                          (rp'.FStar_Tactics_Types.all_implicits);
                                                        FStar_Tactics_Types.goals
                                                          =
                                                          (FStar_Compiler_List.op_At
                                                             lp'.FStar_Tactics_Types.goals
                                                             rp'.FStar_Tactics_Types.goals);
                                                        FStar_Tactics_Types.smt_goals
                                                          =
                                                          (FStar_Compiler_List.op_At
                                                             lp'.FStar_Tactics_Types.smt_goals
                                                             (FStar_Compiler_List.op_At
                                                                rp'.FStar_Tactics_Types.smt_goals
                                                                p.FStar_Tactics_Types.smt_goals));
                                                        FStar_Tactics_Types.depth
                                                          =
                                                          (rp'.FStar_Tactics_Types.depth);
                                                        FStar_Tactics_Types.__dump
                                                          =
                                                          (rp'.FStar_Tactics_Types.__dump);
                                                        FStar_Tactics_Types.psc
                                                          =
                                                          (rp'.FStar_Tactics_Types.psc);
                                                        FStar_Tactics_Types.entry_range
                                                          =
                                                          (rp'.FStar_Tactics_Types.entry_range);
                                                        FStar_Tactics_Types.guard_policy
                                                          =
                                                          (rp'.FStar_Tactics_Types.guard_policy);
                                                        FStar_Tactics_Types.freshness
                                                          =
                                                          (rp'.FStar_Tactics_Types.freshness);
                                                        FStar_Tactics_Types.tac_verb_dbg
                                                          =
                                                          (rp'.FStar_Tactics_Types.tac_verb_dbg);
                                                        FStar_Tactics_Types.local_state
                                                          =
                                                          (rp'.FStar_Tactics_Types.local_state);
                                                        FStar_Tactics_Types.urgency
                                                          =
                                                          (rp'.FStar_Tactics_Types.urgency)
                                                      } in
                                                    let uu___6 =
                                                      FStar_Tactics_Monad.set
                                                        p' in
                                                    FStar_Tactics_Monad.bind
                                                      uu___6
                                                      (fun uu___7 ->
                                                         FStar_Tactics_Monad.bind
                                                           FStar_Tactics_Monad.remove_solved_goals
                                                           (fun uu___8 ->
                                                              FStar_Tactics_Monad.ret
                                                                (a1, b1)))))))))))
let focus : 'a . 'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac =
  fun f ->
    let uu___ = divide FStar_BigInt.one f FStar_Tactics_Monad.idtac in
    FStar_Tactics_Monad.bind uu___
      (fun uu___1 ->
         match uu___1 with | (a1, ()) -> FStar_Tactics_Monad.ret a1)
let rec map :
  'a . 'a FStar_Tactics_Monad.tac -> 'a Prims.list FStar_Tactics_Monad.tac =
  fun tau ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun p ->
         match p.FStar_Tactics_Types.goals with
         | [] -> FStar_Tactics_Monad.ret []
         | uu___::uu___1 ->
             let uu___2 =
               let uu___3 = map tau in divide FStar_BigInt.one tau uu___3 in
             FStar_Tactics_Monad.bind uu___2
               (fun uu___3 ->
                  match uu___3 with
                  | (h, t) -> FStar_Tactics_Monad.ret (h :: t)))
let (seq :
  unit FStar_Tactics_Monad.tac ->
    unit FStar_Tactics_Monad.tac -> unit FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let uu___ =
        FStar_Tactics_Monad.bind t1
          (fun uu___1 ->
             let uu___2 = map t2 in
             FStar_Tactics_Monad.bind uu___2
               (fun uu___3 -> FStar_Tactics_Monad.ret ())) in
      focus uu___
let (should_check_goal_uvar :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.should_check_uvar) =
  fun g ->
    FStar_Syntax_Util.ctx_uvar_should_check
      g.FStar_Tactics_Types.goal_ctx_uvar
let (goal_typedness_deps :
  FStar_Tactics_Types.goal -> FStar_Syntax_Syntax.ctx_uvar Prims.list) =
  fun g ->
    FStar_Syntax_Util.ctx_uvar_typedness_deps
      g.FStar_Tactics_Types.goal_ctx_uvar
let (bnorm_and_replace :
  FStar_Tactics_Types.goal -> unit FStar_Tactics_Monad.tac) =
  fun g -> let uu___ = bnorm_goal g in FStar_Tactics_Monad.replace_cur uu___
let (arrow_one :
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term ->
      (FStar_TypeChecker_Env.env * FStar_Syntax_Syntax.binder *
        FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option)
  =
  fun env1 ->
    fun t ->
      let uu___ = FStar_Syntax_Util.arrow_one_ln t in
      match uu___ with
      | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (b, c) ->
          let uu___1 = FStar_TypeChecker_Core.open_binders_in_comp env1 [b] c in
          (match uu___1 with
           | (env2, b1::[], c1) ->
               FStar_Pervasives_Native.Some (env2, b1, c1))
let (intro : unit -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu___2 =
             let uu___3 = FStar_Tactics_Types.goal_env goal in
             let uu___4 =
               let uu___5 = FStar_Tactics_Types.goal_env goal in
               let uu___6 = FStar_Tactics_Types.goal_type goal in
               whnf uu___5 uu___6 in
             arrow_one uu___3 uu___4 in
           match uu___2 with
           | FStar_Pervasives_Native.Some (env', b, c) ->
               let uu___3 =
                 let uu___4 = FStar_Syntax_Util.is_total_comp c in
                 Prims.op_Negation uu___4 in
               if uu___3
               then FStar_Tactics_Monad.fail "Codomain is effectful"
               else
                 (let typ' = FStar_Syntax_Util.comp_result c in
                  let uu___5 =
                    let uu___6 =
                      let uu___7 = should_check_goal_uvar goal in
                      FStar_Pervasives_Native.Some uu___7 in
                    let uu___7 = goal_typedness_deps goal in
                    FStar_Tactics_Monad.new_uvar "intro" env' typ' uu___6
                      uu___7 (rangeof goal) in
                  FStar_Tactics_Monad.op_let_Bang uu___5
                    (fun uu___6 ->
                       match uu___6 with
                       | (body, ctx_uvar) ->
                           let sol =
                             let uu___7 =
                               let uu___8 =
                                 FStar_Syntax_Util.residual_comp_of_comp c in
                               FStar_Pervasives_Native.Some uu___8 in
                             FStar_Syntax_Util.abs [b] body uu___7 in
                           let uu___7 = set_solution goal sol in
                           FStar_Tactics_Monad.op_let_Bang uu___7
                             (fun uu___8 ->
                                let g =
                                  FStar_Tactics_Types.mk_goal env' ctx_uvar
                                    goal.FStar_Tactics_Types.opts
                                    goal.FStar_Tactics_Types.is_guard
                                    goal.FStar_Tactics_Types.label in
                                let uu___9 = bnorm_and_replace g in
                                FStar_Tactics_Monad.op_let_Bang uu___9
                                  (fun uu___10 -> FStar_Tactics_Monad.ret b))))
           | FStar_Pervasives_Native.None ->
               let uu___3 =
                 let uu___4 = FStar_Tactics_Types.goal_env goal in
                 let uu___5 = FStar_Tactics_Types.goal_type goal in
                 tts uu___4 uu___5 in
               fail1 "goal is not an arrow (%s)" uu___3) in
    FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "intro")
      uu___1
let (intro_rec :
  unit ->
    (FStar_Syntax_Syntax.binder * FStar_Syntax_Syntax.binder)
      FStar_Tactics_Monad.tac)
  =
  fun uu___ ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun goal ->
         FStar_Compiler_Util.print_string
           "WARNING (intro_rec): calling this is known to cause normalizer loops\n";
         FStar_Compiler_Util.print_string
           "WARNING (intro_rec): proceed at your own risk...\n";
         (let uu___3 =
            let uu___4 = FStar_Tactics_Types.goal_env goal in
            let uu___5 =
              let uu___6 = FStar_Tactics_Types.goal_env goal in
              let uu___7 = FStar_Tactics_Types.goal_type goal in
              whnf uu___6 uu___7 in
            arrow_one uu___4 uu___5 in
          match uu___3 with
          | FStar_Pervasives_Native.Some (env', b, c) ->
              let uu___4 =
                let uu___5 = FStar_Syntax_Util.is_total_comp c in
                Prims.op_Negation uu___5 in
              if uu___4
              then FStar_Tactics_Monad.fail "Codomain is effectful"
              else
                (let bv =
                   let uu___6 = FStar_Tactics_Types.goal_type goal in
                   FStar_Syntax_Syntax.gen_bv "__recf"
                     FStar_Pervasives_Native.None uu___6 in
                 let uu___6 =
                   let uu___7 =
                     let uu___8 = should_check_goal_uvar goal in
                     FStar_Pervasives_Native.Some uu___8 in
                   let uu___8 = goal_typedness_deps goal in
                   FStar_Tactics_Monad.new_uvar "intro_rec" env'
                     (FStar_Syntax_Util.comp_result c) uu___7 uu___8
                     (rangeof goal) in
                 FStar_Tactics_Monad.op_let_Bang uu___6
                   (fun uu___7 ->
                      match uu___7 with
                      | (u, ctx_uvar_u) ->
                          let lb =
                            let uu___8 = FStar_Tactics_Types.goal_type goal in
                            let uu___9 =
                              FStar_Syntax_Util.abs [b] u
                                FStar_Pervasives_Native.None in
                            FStar_Syntax_Util.mk_letbinding
                              (FStar_Pervasives.Inl bv) [] uu___8
                              FStar_Parser_Const.effect_Tot_lid uu___9 []
                              FStar_Compiler_Range_Type.dummyRange in
                          let body = FStar_Syntax_Syntax.bv_to_name bv in
                          let uu___8 =
                            FStar_Syntax_Subst.close_let_rec [lb] body in
                          (match uu___8 with
                           | (lbs, body1) ->
                               let tm =
                                 let uu___9 =
                                   let uu___10 =
                                     FStar_Tactics_Types.goal_witness goal in
                                   uu___10.FStar_Syntax_Syntax.pos in
                                 FStar_Syntax_Syntax.mk
                                   (FStar_Syntax_Syntax.Tm_let
                                      {
                                        FStar_Syntax_Syntax.lbs = (true, lbs);
                                        FStar_Syntax_Syntax.body1 = body1
                                      }) uu___9 in
                               let uu___9 = set_solution goal tm in
                               FStar_Tactics_Monad.op_let_Bang uu___9
                                 (fun uu___10 ->
                                    let uu___11 =
                                      bnorm_and_replace
                                        {
                                          FStar_Tactics_Types.goal_main_env =
                                            (goal.FStar_Tactics_Types.goal_main_env);
                                          FStar_Tactics_Types.goal_ctx_uvar =
                                            ctx_uvar_u;
                                          FStar_Tactics_Types.opts =
                                            (goal.FStar_Tactics_Types.opts);
                                          FStar_Tactics_Types.is_guard =
                                            (goal.FStar_Tactics_Types.is_guard);
                                          FStar_Tactics_Types.label =
                                            (goal.FStar_Tactics_Types.label)
                                        } in
                                    FStar_Tactics_Monad.op_let_Bang uu___11
                                      (fun uu___12 ->
                                         let uu___13 =
                                           let uu___14 =
                                             FStar_Syntax_Syntax.mk_binder bv in
                                           (uu___14, b) in
                                         FStar_Tactics_Monad.ret uu___13)))))
          | FStar_Pervasives_Native.None ->
              let uu___4 =
                let uu___5 = FStar_Tactics_Types.goal_env goal in
                let uu___6 = FStar_Tactics_Types.goal_type goal in
                tts uu___5 uu___6 in
              fail1 "intro_rec: goal is not an arrow (%s)" uu___4))
let (norm :
  FStar_Pervasives.norm_step Prims.list -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu___ =
           FStar_Tactics_Monad.if_verbose
             (fun uu___1 ->
                let uu___2 =
                  let uu___3 = FStar_Tactics_Types.goal_witness goal in
                  FStar_Syntax_Print.term_to_string uu___3 in
                FStar_Compiler_Util.print1 "norm: witness = %s\n" uu___2) in
         FStar_Tactics_Monad.op_let_Bang uu___
           (fun uu___1 ->
              let steps =
                let uu___2 = FStar_TypeChecker_Cfg.translate_norm_steps s in
                FStar_Compiler_List.op_At
                  [FStar_TypeChecker_Env.Reify;
                  FStar_TypeChecker_Env.UnfoldTac] uu___2 in
              let t =
                let uu___2 = FStar_Tactics_Types.goal_env goal in
                let uu___3 = FStar_Tactics_Types.goal_type goal in
                normalize steps uu___2 uu___3 in
              let uu___2 = goal_with_type goal t in
              FStar_Tactics_Monad.replace_cur uu___2))
let (norm_term_env :
  env ->
    FStar_Pervasives.norm_step Prims.list ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun s ->
      fun t ->
        let uu___ =
          FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
            (fun ps ->
               let uu___1 =
                 FStar_Tactics_Monad.if_verbose
                   (fun uu___2 ->
                      let uu___3 = FStar_Syntax_Print.term_to_string t in
                      FStar_Compiler_Util.print1 "norm_term_env: t = %s\n"
                        uu___3) in
               FStar_Tactics_Monad.op_let_Bang uu___1
                 (fun uu___2 ->
                    let uu___3 = __tc_lax e t in
                    FStar_Tactics_Monad.op_let_Bang uu___3
                      (fun uu___4 ->
                         match uu___4 with
                         | (t1, uu___5, uu___6) ->
                             let steps =
                               let uu___7 =
                                 FStar_TypeChecker_Cfg.translate_norm_steps s in
                               FStar_Compiler_List.op_At
                                 [FStar_TypeChecker_Env.Reify;
                                 FStar_TypeChecker_Env.UnfoldTac] uu___7 in
                             let t2 =
                               normalize steps
                                 ps.FStar_Tactics_Types.main_context t1 in
                             let uu___7 =
                               FStar_Tactics_Monad.if_verbose
                                 (fun uu___8 ->
                                    let uu___9 =
                                      FStar_Syntax_Print.term_to_string t2 in
                                    FStar_Compiler_Util.print1
                                      "norm_term_env: t' = %s\n" uu___9) in
                             FStar_Tactics_Monad.op_let_Bang uu___7
                               (fun uu___8 -> FStar_Tactics_Monad.ret t2)))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "norm_term") uu___
let (refine_intro : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu___2 =
             let uu___3 = FStar_Tactics_Types.goal_env g in
             let uu___4 = FStar_Tactics_Types.goal_type g in
             FStar_TypeChecker_Rel.base_and_refinement uu___3 uu___4 in
           match uu___2 with
           | (uu___3, FStar_Pervasives_Native.None) ->
               FStar_Tactics_Monad.fail "not a refinement"
           | (t, FStar_Pervasives_Native.Some (bv, phi)) ->
               (mark_goal_implicit_already_checked g;
                (let g1 = goal_with_type g t in
                 let uu___4 =
                   let uu___5 =
                     let uu___6 =
                       let uu___7 = FStar_Syntax_Syntax.mk_binder bv in
                       [uu___7] in
                     FStar_Syntax_Subst.open_term uu___6 phi in
                   match uu___5 with
                   | (bvs, phi1) ->
                       let uu___6 =
                         let uu___7 = FStar_Compiler_List.hd bvs in
                         uu___7.FStar_Syntax_Syntax.binder_bv in
                       (uu___6, phi1) in
                 match uu___4 with
                 | (bv1, phi1) ->
                     let uu___5 =
                       let uu___6 = FStar_Tactics_Types.goal_env g in
                       let uu___7 =
                         let uu___8 =
                           let uu___9 =
                             let uu___10 =
                               let uu___11 =
                                 FStar_Tactics_Types.goal_witness g in
                               (bv1, uu___11) in
                             FStar_Syntax_Syntax.NT uu___10 in
                           [uu___9] in
                         FStar_Syntax_Subst.subst uu___8 phi1 in
                       let uu___8 =
                         let uu___9 = should_check_goal_uvar g in
                         FStar_Pervasives_Native.Some uu___9 in
                       FStar_Tactics_Monad.mk_irrelevant_goal
                         "refine_intro refinement" uu___6 uu___7 uu___8
                         (rangeof g) g.FStar_Tactics_Types.opts
                         g.FStar_Tactics_Types.label in
                     FStar_Tactics_Monad.op_let_Bang uu___5
                       (fun g2 ->
                          FStar_Tactics_Monad.op_let_Bang
                            FStar_Tactics_Monad.dismiss
                            (fun uu___6 ->
                               FStar_Tactics_Monad.add_goals [g1; g2]))))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "refine_intro") uu___1
let (__exact_now :
  Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun set_expected_typ ->
    fun t ->
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let env1 =
             if set_expected_typ
             then
               let uu___ = FStar_Tactics_Types.goal_env goal in
               let uu___1 = FStar_Tactics_Types.goal_type goal in
               FStar_TypeChecker_Env.set_expected_typ uu___ uu___1
             else FStar_Tactics_Types.goal_env goal in
           let uu___ = __tc env1 t in
           FStar_Tactics_Monad.op_let_Bang uu___
             (fun uu___1 ->
                match uu___1 with
                | (t1, typ, guard) ->
                    let uu___2 =
                      FStar_Tactics_Monad.if_verbose
                        (fun uu___3 ->
                           let uu___4 = FStar_Syntax_Print.term_to_string typ in
                           let uu___5 =
                             let uu___6 = FStar_Tactics_Types.goal_env goal in
                             FStar_TypeChecker_Rel.guard_to_string uu___6
                               guard in
                           FStar_Compiler_Util.print2
                             "__exact_now: got type %s\n__exact_now: and guard %s\n"
                             uu___4 uu___5) in
                    FStar_Tactics_Monad.op_let_Bang uu___2
                      (fun uu___3 ->
                         let uu___4 =
                           let uu___5 = FStar_Tactics_Types.goal_env goal in
                           let uu___6 =
                             let uu___7 = should_check_goal_uvar goal in
                             FStar_Pervasives_Native.Some uu___7 in
                           proc_guard "__exact typing" uu___5 guard uu___6
                             (rangeof goal) in
                         FStar_Tactics_Monad.op_let_Bang uu___4
                           (fun uu___5 ->
                              let uu___6 =
                                FStar_Tactics_Monad.if_verbose
                                  (fun uu___7 ->
                                     let uu___8 =
                                       FStar_Syntax_Print.term_to_string typ in
                                     let uu___9 =
                                       let uu___10 =
                                         FStar_Tactics_Types.goal_type goal in
                                       FStar_Syntax_Print.term_to_string
                                         uu___10 in
                                     FStar_Compiler_Util.print2
                                       "__exact_now: unifying %s and %s\n"
                                       uu___8 uu___9) in
                              FStar_Tactics_Monad.op_let_Bang uu___6
                                (fun uu___7 ->
                                   let uu___8 =
                                     let uu___9 =
                                       FStar_Tactics_Types.goal_env goal in
                                     let uu___10 =
                                       FStar_Tactics_Types.goal_type goal in
                                     do_unify true uu___9 typ uu___10 in
                                   FStar_Tactics_Monad.op_let_Bang uu___8
                                     (fun b ->
                                        if b
                                        then
                                          (mark_goal_implicit_already_checked
                                             goal;
                                           solve goal t1)
                                        else
                                          (let uu___10 =
                                             let uu___11 =
                                               let uu___12 =
                                                 FStar_Tactics_Types.goal_env
                                                   goal in
                                               tts uu___12 in
                                             let uu___12 =
                                               FStar_Tactics_Types.goal_type
                                                 goal in
                                             FStar_TypeChecker_Err.print_discrepancy
                                               uu___11 typ uu___12 in
                                           match uu___10 with
                                           | (typ1, goalt) ->
                                               let uu___11 =
                                                 let uu___12 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 tts uu___12 t1 in
                                               let uu___12 =
                                                 let uu___13 =
                                                   FStar_Tactics_Types.goal_env
                                                     goal in
                                                 let uu___14 =
                                                   FStar_Tactics_Types.goal_witness
                                                     goal in
                                                 tts uu___13 uu___14 in
                                               fail4
                                                 "%s : %s does not exactly solve the goal %s (witness = %s)"
                                                 uu___11 typ1 goalt uu___12)))))))
let (t_exact :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun try_refine ->
    fun set_expected_typ ->
      fun tm ->
        let uu___ =
          let uu___1 =
            FStar_Tactics_Monad.if_verbose
              (fun uu___2 ->
                 let uu___3 = FStar_Syntax_Print.term_to_string tm in
                 FStar_Compiler_Util.print1 "t_exact: tm = %s\n" uu___3) in
          FStar_Tactics_Monad.op_let_Bang uu___1
            (fun uu___2 ->
               let uu___3 =
                 let uu___4 = __exact_now set_expected_typ tm in
                 FStar_Tactics_Monad.catch uu___4 in
               FStar_Tactics_Monad.op_let_Bang uu___3
                 (fun uu___4 ->
                    match uu___4 with
                    | FStar_Pervasives.Inr r -> FStar_Tactics_Monad.ret ()
                    | FStar_Pervasives.Inl e when
                        Prims.op_Negation try_refine ->
                        FStar_Tactics_Monad.traise e
                    | FStar_Pervasives.Inl e ->
                        let uu___5 =
                          FStar_Tactics_Monad.if_verbose
                            (fun uu___6 ->
                               FStar_Compiler_Util.print_string
                                 "__exact_now failed, trying refine...\n") in
                        FStar_Tactics_Monad.op_let_Bang uu___5
                          (fun uu___6 ->
                             let uu___7 =
                               let uu___8 =
                                 let uu___9 = norm [FStar_Pervasives.Delta] in
                                 FStar_Tactics_Monad.op_let_Bang uu___9
                                   (fun uu___10 ->
                                      let uu___11 = refine_intro () in
                                      FStar_Tactics_Monad.op_let_Bang uu___11
                                        (fun uu___12 ->
                                           __exact_now set_expected_typ tm)) in
                               FStar_Tactics_Monad.catch uu___8 in
                             FStar_Tactics_Monad.op_let_Bang uu___7
                               (fun uu___8 ->
                                  match uu___8 with
                                  | FStar_Pervasives.Inr r ->
                                      let uu___9 =
                                        FStar_Tactics_Monad.if_verbose
                                          (fun uu___10 ->
                                             FStar_Compiler_Util.print_string
                                               "__exact_now: failed after refining too\n") in
                                      FStar_Tactics_Monad.op_let_Bang uu___9
                                        (fun uu___10 ->
                                           FStar_Tactics_Monad.ret ())
                                  | FStar_Pervasives.Inl uu___9 ->
                                      let uu___10 =
                                        FStar_Tactics_Monad.if_verbose
                                          (fun uu___11 ->
                                             FStar_Compiler_Util.print_string
                                               "__exact_now: was not a refinement\n") in
                                      FStar_Tactics_Monad.op_let_Bang uu___10
                                        (fun uu___11 ->
                                           FStar_Tactics_Monad.traise e))))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "exact") uu___
let (try_unify_by_application :
  FStar_Syntax_Syntax.should_check_uvar FStar_Pervasives_Native.option ->
    Prims.bool ->
      env ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Compiler_Range_Type.range ->
              (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.aqual *
                FStar_Syntax_Syntax.ctx_uvar) Prims.list
                FStar_Tactics_Monad.tac)
  =
  fun should_check ->
    fun only_match ->
      fun e ->
        fun ty1 ->
          fun ty2 ->
            fun rng ->
              let f = if only_match then do_match else do_unify in
              let must_tot = true in
              let rec aux acc typedness_deps ty11 =
                let uu___ = f must_tot e ty2 ty11 in
                FStar_Tactics_Monad.op_let_Bang uu___
                  (fun uu___1 ->
                     if uu___1
                     then FStar_Tactics_Monad.ret acc
                     else
                       (let uu___2 = FStar_Syntax_Util.arrow_one ty11 in
                        match uu___2 with
                        | FStar_Pervasives_Native.None ->
                            let uu___3 = tts e ty11 in
                            let uu___4 = tts e ty2 in
                            fail2 "Could not instantiate, %s to %s" uu___3
                              uu___4
                        | FStar_Pervasives_Native.Some (b, c) ->
                            let uu___3 =
                              let uu___4 = FStar_Syntax_Util.is_total_comp c in
                              Prims.op_Negation uu___4 in
                            if uu___3
                            then
                              FStar_Tactics_Monad.fail
                                "Codomain is effectful"
                            else
                              (let uu___5 =
                                 FStar_Tactics_Monad.new_uvar "apply arg" e
                                   (b.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort
                                   should_check typedness_deps rng in
                               FStar_Tactics_Monad.op_let_Bang uu___5
                                 (fun uu___6 ->
                                    match uu___6 with
                                    | (uvt, uv) ->
                                        let uu___7 =
                                          FStar_Tactics_Monad.if_verbose
                                            (fun uu___8 ->
                                               let uu___9 =
                                                 FStar_Syntax_Print.ctx_uvar_to_string
                                                   uv in
                                               FStar_Compiler_Util.print1
                                                 "t_apply: generated uvar %s\n"
                                                 uu___9) in
                                        FStar_Tactics_Monad.op_let_Bang
                                          uu___7
                                          (fun uu___8 ->
                                             let typ =
                                               FStar_Syntax_Util.comp_result
                                                 c in
                                             let typ' =
                                               FStar_Syntax_Subst.subst
                                                 [FStar_Syntax_Syntax.NT
                                                    ((b.FStar_Syntax_Syntax.binder_bv),
                                                      uvt)] typ in
                                             let uu___9 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   FStar_Syntax_Util.aqual_of_binder
                                                     b in
                                                 (uvt, uu___11, uv) in
                                               uu___10 :: acc in
                                             aux uu___9 (uv ::
                                               typedness_deps) typ'))))) in
              aux [] [] ty1
let (apply_implicits_as_goals :
  FStar_TypeChecker_Env.env ->
    FStar_Tactics_Types.goal FStar_Pervasives_Native.option ->
      (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.ctx_uvar) Prims.list ->
        FStar_Tactics_Types.goal Prims.list Prims.list
          FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun gl ->
      fun imps ->
        let one_implicit_as_goal uu___ =
          match uu___ with
          | (term, ctx_uvar) ->
              let uu___1 = FStar_Syntax_Util.head_and_args term in
              (match uu___1 with
               | (hd, uu___2) ->
                   let uu___3 =
                     let uu___4 = FStar_Syntax_Subst.compress hd in
                     uu___4.FStar_Syntax_Syntax.n in
                   (match uu___3 with
                    | FStar_Syntax_Syntax.Tm_uvar (ctx_uvar1, uu___4) ->
                        let gl1 =
                          match gl with
                          | FStar_Pervasives_Native.None ->
                              let uu___5 = FStar_Options.peek () in
                              FStar_Tactics_Types.mk_goal env1 ctx_uvar1
                                uu___5 true "goal for unsolved implicit"
                          | FStar_Pervasives_Native.Some gl2 ->
                              {
                                FStar_Tactics_Types.goal_main_env =
                                  (gl2.FStar_Tactics_Types.goal_main_env);
                                FStar_Tactics_Types.goal_ctx_uvar = ctx_uvar1;
                                FStar_Tactics_Types.opts =
                                  (gl2.FStar_Tactics_Types.opts);
                                FStar_Tactics_Types.is_guard =
                                  (gl2.FStar_Tactics_Types.is_guard);
                                FStar_Tactics_Types.label =
                                  (gl2.FStar_Tactics_Types.label)
                              } in
                        let gl2 = bnorm_goal gl1 in
                        FStar_Tactics_Monad.ret [gl2]
                    | uu___4 -> FStar_Tactics_Monad.ret [])) in
        FStar_Compiler_Effect.op_Bar_Greater imps
          (FStar_Tactics_Monad.mapM one_implicit_as_goal)
let (t_apply :
  Prims.bool ->
    Prims.bool ->
      Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun uopt ->
    fun only_match ->
      fun tc_resolved_uvars ->
        fun tm ->
          let uu___ =
            let tc_resolved_uvars1 = true in
            let uu___1 =
              FStar_Tactics_Monad.if_verbose
                (fun uu___2 ->
                   let uu___3 = FStar_Compiler_Util.string_of_bool uopt in
                   let uu___4 = FStar_Compiler_Util.string_of_bool only_match in
                   let uu___5 =
                     FStar_Compiler_Util.string_of_bool tc_resolved_uvars1 in
                   let uu___6 = FStar_Syntax_Print.term_to_string tm in
                   FStar_Compiler_Util.print4
                     "t_apply: uopt %s, only_match %s, tc_resolved_uvars %s, tm = %s\n"
                     uu___3 uu___4 uu___5 uu___6) in
            FStar_Tactics_Monad.op_let_Bang uu___1
              (fun uu___2 ->
                 FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
                   (fun ps ->
                      FStar_Tactics_Monad.op_let_Bang
                        FStar_Tactics_Monad.cur_goal
                        (fun goal ->
                           let e = FStar_Tactics_Types.goal_env goal in
                           let should_check = should_check_goal_uvar goal in
                           FStar_Tactics_Monad.register_goal goal;
                           (let uu___4 = __tc e tm in
                            FStar_Tactics_Monad.op_let_Bang uu___4
                              (fun uu___5 ->
                                 match uu___5 with
                                 | (tm1, typ, guard) ->
                                     let uu___6 =
                                       FStar_Tactics_Monad.if_verbose
                                         (fun uu___7 ->
                                            let uu___8 =
                                              FStar_Syntax_Print.term_to_string
                                                tm1 in
                                            let uu___9 =
                                              FStar_Tactics_Printing.goal_to_string_verbose
                                                goal in
                                            let uu___10 =
                                              FStar_TypeChecker_Env.print_gamma
                                                e.FStar_TypeChecker_Env.gamma in
                                            let uu___11 =
                                              FStar_Syntax_Print.term_to_string
                                                typ in
                                            let uu___12 =
                                              FStar_TypeChecker_Rel.guard_to_string
                                                e guard in
                                            FStar_Compiler_Util.print5
                                              "t_apply: tm = %s\nt_apply: goal = %s\nenv.gamma=%s\ntyp=%s\nguard=%s\n"
                                              uu___8 uu___9 uu___10 uu___11
                                              uu___12) in
                                     FStar_Tactics_Monad.op_let_Bang uu___6
                                       (fun uu___7 ->
                                          let typ1 = bnorm e typ in
                                          let uu___8 =
                                            let uu___9 =
                                              FStar_Tactics_Types.goal_type
                                                goal in
                                            try_unify_by_application
                                              (FStar_Pervasives_Native.Some
                                                 should_check) only_match e
                                              typ1 uu___9 (rangeof goal) in
                                          FStar_Tactics_Monad.op_let_Bang
                                            uu___8
                                            (fun uvs ->
                                               let uu___9 =
                                                 FStar_Tactics_Monad.if_verbose
                                                   (fun uu___10 ->
                                                      let uu___11 =
                                                        (FStar_Common.string_of_list
                                                           ())
                                                          (fun uu___12 ->
                                                             match uu___12
                                                             with
                                                             | (t, uu___13,
                                                                uu___14) ->
                                                                 FStar_Syntax_Print.term_to_string
                                                                   t) uvs in
                                                      FStar_Compiler_Util.print1
                                                        "t_apply: found args = %s\n"
                                                        uu___11) in
                                               FStar_Tactics_Monad.op_let_Bang
                                                 uu___9
                                                 (fun uu___10 ->
                                                    let w =
                                                      FStar_Compiler_List.fold_right
                                                        (fun uu___11 ->
                                                           fun w1 ->
                                                             match uu___11
                                                             with
                                                             | (uvt, q,
                                                                uu___12) ->
                                                                 FStar_Syntax_Util.mk_app
                                                                   w1
                                                                   [(uvt, q)])
                                                        uvs tm1 in
                                                    let uvset =
                                                      let uu___11 =
                                                        FStar_Syntax_Free.new_uv_set
                                                          () in
                                                      FStar_Compiler_List.fold_right
                                                        (fun uu___12 ->
                                                           fun s ->
                                                             match uu___12
                                                             with
                                                             | (uu___13,
                                                                uu___14, uv)
                                                                 ->
                                                                 let uu___15
                                                                   =
                                                                   let uu___16
                                                                    =
                                                                    FStar_Syntax_Util.ctx_uvar_typ
                                                                    uv in
                                                                   FStar_Syntax_Free.uvars
                                                                    uu___16 in
                                                                 FStar_Compiler_Util.set_union
                                                                   s uu___15)
                                                        uvs uu___11 in
                                                    let free_in_some_goal uv
                                                      =
                                                      FStar_Compiler_Util.set_mem
                                                        uv uvset in
                                                    let uu___11 =
                                                      solve' goal w in
                                                    FStar_Tactics_Monad.op_let_Bang
                                                      uu___11
                                                      (fun uu___12 ->
                                                         let uvt_uv_l =
                                                           FStar_Compiler_Effect.op_Bar_Greater
                                                             uvs
                                                             (FStar_Compiler_List.map
                                                                (fun uu___13
                                                                   ->
                                                                   match uu___13
                                                                   with
                                                                   | 
                                                                   (uvt, _q,
                                                                    uv) ->
                                                                    (uvt, uv))) in
                                                         let uu___13 =
                                                           apply_implicits_as_goals
                                                             e
                                                             (FStar_Pervasives_Native.Some
                                                                goal)
                                                             uvt_uv_l in
                                                         FStar_Tactics_Monad.op_let_Bang
                                                           uu___13
                                                           (fun sub_goals ->
                                                              let sub_goals1
                                                                =
                                                                let uu___14 =
                                                                  let uu___15
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    (FStar_Compiler_List.flatten
                                                                    sub_goals)
                                                                    (FStar_Compiler_List.filter
                                                                    (fun g ->
                                                                    let uu___16
                                                                    =
                                                                    uopt &&
                                                                    (free_in_some_goal
                                                                    g.FStar_Tactics_Types.goal_ctx_uvar) in
                                                                    Prims.op_Negation
                                                                    uu___16)) in
                                                                  FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___15
                                                                    (
                                                                    FStar_Compiler_List.map
                                                                    bnorm_goal) in
                                                                FStar_Compiler_Effect.op_Bar_Greater
                                                                  uu___14
                                                                  FStar_Compiler_List.rev in
                                                              let uu___14 =
                                                                FStar_Tactics_Monad.add_goals
                                                                  sub_goals1 in
                                                              FStar_Tactics_Monad.op_let_Bang
                                                                uu___14
                                                                (fun uu___15
                                                                   ->
                                                                   proc_guard
                                                                    "apply guard"
                                                                    e guard
                                                                    (FStar_Pervasives_Native.Some
                                                                    should_check)
                                                                    (rangeof
                                                                    goal)))))))))))) in
          FStar_Compiler_Effect.op_Less_Bar
            (FStar_Tactics_Monad.wrap_err "apply") uu___
let (lemma_or_sq :
  FStar_Syntax_Syntax.comp ->
    (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.term)
      FStar_Pervasives_Native.option)
  =
  fun c ->
    let uu___ = FStar_Syntax_Util.comp_eff_name_res_and_args c in
    match uu___ with
    | (eff_name, res, args) ->
        let uu___1 =
          FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Lemma_lid in
        if uu___1
        then
          let uu___2 =
            match args with
            | pre::post::uu___3 ->
                ((FStar_Pervasives_Native.fst pre),
                  (FStar_Pervasives_Native.fst post))
            | uu___3 -> failwith "apply_lemma: impossible: not a lemma" in
          (match uu___2 with
           | (pre, post) ->
               let post1 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Syntax_Syntax.as_arg FStar_Syntax_Util.exp_unit in
                   [uu___4] in
                 FStar_Syntax_Util.mk_app post uu___3 in
               FStar_Pervasives_Native.Some (pre, post1))
        else
          (let uu___3 =
             (FStar_Syntax_Util.is_pure_effect eff_name) ||
               (FStar_Syntax_Util.is_ghost_effect eff_name) in
           if uu___3
           then
             let uu___4 = FStar_Syntax_Util.un_squash res in
             FStar_Compiler_Util.map_opt uu___4
               (fun post -> (FStar_Syntax_Util.t_true, post))
           else FStar_Pervasives_Native.None)
let rec fold_left :
  'a 'b .
    ('a -> 'b -> 'b FStar_Tactics_Monad.tac) ->
      'b -> 'a Prims.list -> 'b FStar_Tactics_Monad.tac
  =
  fun f ->
    fun e ->
      fun xs ->
        match xs with
        | [] -> FStar_Tactics_Monad.ret e
        | x::xs1 ->
            let uu___ = f x e in
            FStar_Tactics_Monad.bind uu___ (fun e' -> fold_left f e' xs1)
let (t_apply_lemma :
  Prims.bool ->
    Prims.bool -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun noinst ->
    fun noinst_lhs ->
      fun tm ->
        let uu___ =
          let uu___1 =
            FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
              (fun ps ->
                 let uu___2 =
                   FStar_Tactics_Monad.if_verbose
                     (fun uu___3 ->
                        let uu___4 = FStar_Syntax_Print.term_to_string tm in
                        FStar_Compiler_Util.print1 "apply_lemma: tm = %s\n"
                          uu___4) in
                 FStar_Tactics_Monad.op_let_Bang uu___2
                   (fun uu___3 ->
                      let is_unit_t t =
                        let uu___4 =
                          let uu___5 = FStar_Syntax_Subst.compress t in
                          uu___5.FStar_Syntax_Syntax.n in
                        match uu___4 with
                        | FStar_Syntax_Syntax.Tm_fvar fv when
                            FStar_Syntax_Syntax.fv_eq_lid fv
                              FStar_Parser_Const.unit_lid
                            -> true
                        | uu___5 -> false in
                      FStar_Tactics_Monad.op_let_Bang
                        FStar_Tactics_Monad.cur_goal
                        (fun goal ->
                           let env1 = FStar_Tactics_Types.goal_env goal in
                           FStar_Tactics_Monad.register_goal goal;
                           (let uu___5 = __tc env1 tm in
                            FStar_Tactics_Monad.op_let_Bang uu___5
                              (fun uu___6 ->
                                 match uu___6 with
                                 | (tm1, t, guard) ->
                                     let uu___7 =
                                       FStar_Syntax_Util.arrow_formals_comp t in
                                     (match uu___7 with
                                      | (bs, comp) ->
                                          let uu___8 = lemma_or_sq comp in
                                          (match uu___8 with
                                           | FStar_Pervasives_Native.None ->
                                               FStar_Tactics_Monad.fail
                                                 "not a lemma or squashed function"
                                           | FStar_Pervasives_Native.Some
                                               (pre, post) ->
                                               let uu___9 =
                                                 fold_left
                                                   (fun uu___10 ->
                                                      fun uu___11 ->
                                                        match (uu___10,
                                                                uu___11)
                                                        with
                                                        | ({
                                                             FStar_Syntax_Syntax.binder_bv
                                                               = b;
                                                             FStar_Syntax_Syntax.binder_qual
                                                               = aq;
                                                             FStar_Syntax_Syntax.binder_positivity
                                                               = uu___12;
                                                             FStar_Syntax_Syntax.binder_attrs
                                                               = uu___13;_},
                                                           (uvs, deps, imps,
                                                            subst)) ->
                                                            let b_t =
                                                              FStar_Syntax_Subst.subst
                                                                subst
                                                                b.FStar_Syntax_Syntax.sort in
                                                            let uu___14 =
                                                              is_unit_t b_t in
                                                            if uu___14
                                                            then
                                                              FStar_Compiler_Effect.op_Less_Bar
                                                                FStar_Tactics_Monad.ret
                                                                (((FStar_Syntax_Util.exp_unit,
                                                                    aq) ::
                                                                  uvs), deps,
                                                                  imps,
                                                                  ((FStar_Syntax_Syntax.NT
                                                                    (b,
                                                                    FStar_Syntax_Util.exp_unit))
                                                                  :: subst))
                                                            else
                                                              (let uu___16 =
                                                                 let uu___17
                                                                   =
                                                                   let uu___18
                                                                    =
                                                                    let uu___19
                                                                    =
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    goal
                                                                    should_check_goal_uvar in
                                                                    FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___19
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    match uu___20
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Strict
                                                                    ->
                                                                    FStar_Syntax_Syntax.Allow_ghost
                                                                    "apply lemma uvar"
                                                                    | 
                                                                    x -> x) in
                                                                   FStar_Compiler_Effect.op_Bar_Greater
                                                                    uu___18
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    FStar_Pervasives_Native.Some
                                                                    uu___19) in
                                                                 FStar_Tactics_Monad.new_uvar
                                                                   "apply_lemma"
                                                                   env1 b_t
                                                                   uu___17
                                                                   deps
                                                                   (rangeof
                                                                    goal) in
                                                               FStar_Tactics_Monad.op_let_Bang
                                                                 uu___16
                                                                 (fun uu___17
                                                                    ->
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    (t1, u)
                                                                    ->
                                                                    ((
                                                                    let uu___19
                                                                    =
                                                                    FStar_Compiler_Effect.op_Less_Bar
                                                                    (FStar_TypeChecker_Env.debug
                                                                    env1)
                                                                    (FStar_Options.Other
                                                                    "2635") in
                                                                    if
                                                                    uu___19
                                                                    then
                                                                    let uu___20
                                                                    =
                                                                    FStar_Syntax_Print.ctx_uvar_to_string
                                                                    u in
                                                                    let uu___21
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    tm1 in
                                                                    FStar_Compiler_Util.print2
                                                                    "Apply lemma created a new uvar %s while applying %s\n"
                                                                    uu___20
                                                                    uu___21
                                                                    else ());
                                                                    FStar_Tactics_Monad.ret
                                                                    (((t1,
                                                                    aq) ::
                                                                    uvs), (u
                                                                    :: deps),
                                                                    ((t1, u)
                                                                    :: imps),
                                                                    ((FStar_Syntax_Syntax.NT
                                                                    (b, t1))
                                                                    ::
                                                                    subst))))))
                                                   ([], [], [], []) bs in
                                               FStar_Tactics_Monad.op_let_Bang
                                                 uu___9
                                                 (fun uu___10 ->
                                                    match uu___10 with
                                                    | (uvs, uu___11,
                                                       implicits1, subst) ->
                                                        let implicits2 =
                                                          FStar_Compiler_List.rev
                                                            implicits1 in
                                                        let uvs1 =
                                                          FStar_Compiler_List.rev
                                                            uvs in
                                                        let pre1 =
                                                          FStar_Syntax_Subst.subst
                                                            subst pre in
                                                        let post1 =
                                                          FStar_Syntax_Subst.subst
                                                            subst post in
                                                        let post_u =
                                                          env1.FStar_TypeChecker_Env.universe_of
                                                            env1 post1 in
                                                        let cmp_func =
                                                          if noinst
                                                          then do_match
                                                          else
                                                            if noinst_lhs
                                                            then
                                                              do_match_on_lhs
                                                            else do_unify in
                                                        let uu___12 =
                                                          let must_tot =
                                                            false in
                                                          let uu___13 =
                                                            FStar_Tactics_Types.goal_type
                                                              goal in
                                                          let uu___14 =
                                                            FStar_Syntax_Util.mk_squash
                                                              post_u post1 in
                                                          cmp_func must_tot
                                                            env1 uu___13
                                                            uu___14 in
                                                        FStar_Tactics_Monad.op_let_Bang
                                                          uu___12
                                                          (fun b ->
                                                             if
                                                               Prims.op_Negation
                                                                 b
                                                             then
                                                               let uu___13 =
                                                                 let uu___14
                                                                   =
                                                                   FStar_Syntax_Util.mk_squash
                                                                    post_u
                                                                    post1 in
                                                                 let uu___15
                                                                   =
                                                                   FStar_Tactics_Types.goal_type
                                                                    goal in
                                                                 FStar_TypeChecker_Err.print_discrepancy
                                                                   (tts env1)
                                                                   uu___14
                                                                   uu___15 in
                                                               match uu___13
                                                               with
                                                               | (post2,
                                                                  goalt) ->
                                                                   let uu___14
                                                                    =
                                                                    tts env1
                                                                    tm1 in
                                                                   fail3
                                                                    "Cannot instantiate lemma %s (with postcondition: %s) to match goal (%s)"
                                                                    uu___14
                                                                    post2
                                                                    goalt
                                                             else
                                                               (let goal_sc =
                                                                  should_check_goal_uvar
                                                                    goal in
                                                                let uu___14 =
                                                                  solve' goal
                                                                    FStar_Syntax_Util.exp_unit in
                                                                FStar_Tactics_Monad.op_let_Bang
                                                                  uu___14
                                                                  (fun
                                                                    uu___15
                                                                    ->
                                                                    let is_free_uvar
                                                                    uv t1 =
                                                                    let free_uvars
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    let uu___17
                                                                    =
                                                                    FStar_Syntax_Free.uvars
                                                                    t1 in
                                                                    FStar_Compiler_Util.set_elements
                                                                    uu___17 in
                                                                    FStar_Compiler_List.map
                                                                    (fun x ->
                                                                    x.FStar_Syntax_Syntax.ctx_uvar_head)
                                                                    uu___16 in
                                                                    FStar_Compiler_List.existsML
                                                                    (fun u ->
                                                                    FStar_Syntax_Unionfind.equiv
                                                                    u uv)
                                                                    free_uvars in
                                                                    let appears
                                                                    uv goals
                                                                    =
                                                                    FStar_Compiler_List.existsML
                                                                    (fun g'
                                                                    ->
                                                                    let uu___16
                                                                    =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g' in
                                                                    is_free_uvar
                                                                    uv
                                                                    uu___16)
                                                                    goals in
                                                                    let checkone
                                                                    t1 goals
                                                                    =
                                                                    let uu___16
                                                                    =
                                                                    FStar_Syntax_Util.head_and_args
                                                                    t1 in
                                                                    match uu___16
                                                                    with
                                                                    | 
                                                                    (hd,
                                                                    uu___17)
                                                                    ->
                                                                    (match 
                                                                    hd.FStar_Syntax_Syntax.n
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Tm_uvar
                                                                    (uv,
                                                                    uu___18)
                                                                    ->
                                                                    appears
                                                                    uv.FStar_Syntax_Syntax.ctx_uvar_head
                                                                    goals
                                                                    | 
                                                                    uu___18
                                                                    -> false) in
                                                                    let must_tot
                                                                    = false in
                                                                    let uu___16
                                                                    =
                                                                    apply_implicits_as_goals
                                                                    env1
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal)
                                                                    implicits2 in
                                                                    FStar_Tactics_Monad.op_let_Bang
                                                                    uu___16
                                                                    (fun
                                                                    sub_goals
                                                                    ->
                                                                    let sub_goals1
                                                                    =
                                                                    FStar_Compiler_List.flatten
                                                                    sub_goals in
                                                                    let rec filter'
                                                                    f xs =
                                                                    match xs
                                                                    with
                                                                    | 
                                                                    [] -> []
                                                                    | 
                                                                    x::xs1 ->
                                                                    let uu___17
                                                                    = f x xs1 in
                                                                    if
                                                                    uu___17
                                                                    then
                                                                    let uu___18
                                                                    =
                                                                    filter' f
                                                                    xs1 in x
                                                                    ::
                                                                    uu___18
                                                                    else
                                                                    filter' f
                                                                    xs1 in
                                                                    let sub_goals2
                                                                    =
                                                                    filter'
                                                                    (fun g ->
                                                                    fun goals
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_Tactics_Types.goal_witness
                                                                    g in
                                                                    checkone
                                                                    uu___18
                                                                    goals in
                                                                    Prims.op_Negation
                                                                    uu___17)
                                                                    sub_goals1 in
                                                                    let uu___17
                                                                    =
                                                                    proc_guard
                                                                    "apply_lemma guard"
                                                                    env1
                                                                    guard
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal_sc)
                                                                    (rangeof
                                                                    goal) in
                                                                    FStar_Tactics_Monad.op_let_Bang
                                                                    uu___17
                                                                    (fun
                                                                    uu___18
                                                                    ->
                                                                    let pre_u
                                                                    =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1 pre1 in
                                                                    let uu___19
                                                                    =
                                                                    let uu___20
                                                                    =
                                                                    let uu___21
                                                                    =
                                                                    let uu___22
                                                                    =
                                                                    FStar_TypeChecker_Env.guard_of_guard_formula
                                                                    (FStar_TypeChecker_Common.NonTrivial
                                                                    pre1) in
                                                                    FStar_TypeChecker_Rel.simplify_guard
                                                                    env1
                                                                    uu___22 in
                                                                    uu___21.FStar_TypeChecker_Common.guard_f in
                                                                    match uu___20
                                                                    with
                                                                    | 
                                                                    FStar_TypeChecker_Common.Trivial
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    ()
                                                                    | 
                                                                    FStar_TypeChecker_Common.NonTrivial
                                                                    uu___21
                                                                    ->
                                                                    FStar_Tactics_Monad.add_irrelevant_goal
                                                                    goal
                                                                    "apply_lemma precondition"
                                                                    env1 pre1
                                                                    (FStar_Pervasives_Native.Some
                                                                    goal_sc) in
                                                                    FStar_Tactics_Monad.op_let_Bang
                                                                    uu___19
                                                                    (fun
                                                                    uu___20
                                                                    ->
                                                                    FStar_Tactics_Monad.add_goals
                                                                    sub_goals2)))))))))))))) in
          focus uu___1 in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "apply_lemma") uu___
let (split_env :
  FStar_Syntax_Syntax.bv ->
    env ->
      (env * FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.bv Prims.list)
        FStar_Pervasives_Native.option)
  =
  fun bvar ->
    fun e ->
      let rec aux e1 =
        let uu___ = FStar_TypeChecker_Env.pop_bv e1 in
        match uu___ with
        | FStar_Pervasives_Native.None -> FStar_Pervasives_Native.None
        | FStar_Pervasives_Native.Some (bv', e') ->
            let uu___1 = FStar_Syntax_Syntax.bv_eq bvar bv' in
            if uu___1
            then FStar_Pervasives_Native.Some (e', bv', [])
            else
              (let uu___3 = aux e' in
               FStar_Compiler_Util.map_opt uu___3
                 (fun uu___4 ->
                    match uu___4 with
                    | (e'', bv, bvs) -> (e'', bv, (bv' :: bvs)))) in
      let uu___ = aux e in
      FStar_Compiler_Util.map_opt uu___
        (fun uu___1 ->
           match uu___1 with
           | (e', bv, bvs) -> (e', bv, (FStar_Compiler_List.rev bvs)))
let (subst_goal :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.bv ->
      FStar_Tactics_Types.goal ->
        (FStar_Syntax_Syntax.bv * FStar_Tactics_Types.goal)
          FStar_Pervasives_Native.option FStar_Tactics_Monad.tac)
  =
  fun b1 ->
    fun b2 ->
      fun g ->
        let uu___ =
          let uu___1 = FStar_Tactics_Types.goal_env g in split_env b1 uu___1 in
        match uu___ with
        | FStar_Pervasives_Native.Some (e0, b11, bvs) ->
            let bs =
              FStar_Compiler_List.map FStar_Syntax_Syntax.mk_binder (b11 ::
                bvs) in
            let t = FStar_Tactics_Types.goal_type g in
            let uu___1 =
              let uu___2 = FStar_Syntax_Subst.close_binders bs in
              let uu___3 = FStar_Syntax_Subst.close bs t in (uu___2, uu___3) in
            (match uu___1 with
             | (bs', t') ->
                 let bs'1 =
                   let uu___2 = FStar_Syntax_Syntax.mk_binder b2 in
                   let uu___3 = FStar_Compiler_List.tail bs' in uu___2 ::
                     uu___3 in
                 let uu___2 =
                   FStar_TypeChecker_Core.open_binders_in_term e0 bs'1 t' in
                 (match uu___2 with
                  | (new_env, bs'', t'') ->
                      let b21 =
                        let uu___3 = FStar_Compiler_List.hd bs'' in
                        uu___3.FStar_Syntax_Syntax.binder_bv in
                      let uu___3 =
                        let uu___4 =
                          let uu___5 = should_check_goal_uvar g in
                          FStar_Pervasives_Native.Some uu___5 in
                        let uu___5 = goal_typedness_deps g in
                        FStar_Tactics_Monad.new_uvar "subst_goal" new_env t''
                          uu___4 uu___5 (rangeof g) in
                      FStar_Tactics_Monad.op_let_Bang uu___3
                        (fun uu___4 ->
                           match uu___4 with
                           | (uvt, uv) ->
                               let goal' =
                                 FStar_Tactics_Types.mk_goal new_env uv
                                   g.FStar_Tactics_Types.opts
                                   g.FStar_Tactics_Types.is_guard
                                   g.FStar_Tactics_Types.label in
                               let sol =
                                 let uu___5 =
                                   FStar_Syntax_Util.abs bs'' uvt
                                     FStar_Pervasives_Native.None in
                                 let uu___6 =
                                   FStar_Compiler_List.map
                                     (fun uu___7 ->
                                        match uu___7 with
                                        | {
                                            FStar_Syntax_Syntax.binder_bv =
                                              bv;
                                            FStar_Syntax_Syntax.binder_qual =
                                              q;
                                            FStar_Syntax_Syntax.binder_positivity
                                              = uu___8;
                                            FStar_Syntax_Syntax.binder_attrs
                                              = uu___9;_}
                                            ->
                                            let uu___10 =
                                              FStar_Syntax_Syntax.bv_to_name
                                                bv in
                                            FStar_Syntax_Syntax.as_arg
                                              uu___10) bs in
                                 FStar_Syntax_Util.mk_app uu___5 uu___6 in
                               let uu___5 = set_solution g sol in
                               FStar_Tactics_Monad.op_let_Bang uu___5
                                 (fun uu___6 ->
                                    FStar_Tactics_Monad.ret
                                      (FStar_Pervasives_Native.Some
                                         (b21, goal'))))))
        | FStar_Pervasives_Native.None ->
            FStar_Tactics_Monad.ret FStar_Pervasives_Native.None
let (rewrite : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun h ->
    let uu___ =
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let bv = h.FStar_Syntax_Syntax.binder_bv in
           let uu___1 =
             FStar_Tactics_Monad.if_verbose
               (fun uu___2 ->
                  let uu___3 = FStar_Syntax_Print.bv_to_string bv in
                  let uu___4 =
                    FStar_Syntax_Print.term_to_string
                      bv.FStar_Syntax_Syntax.sort in
                  FStar_Compiler_Util.print2 "+++Rewrite %s : %s\n" uu___3
                    uu___4) in
           FStar_Tactics_Monad.op_let_Bang uu___1
             (fun uu___2 ->
                let uu___3 =
                  let uu___4 = FStar_Tactics_Types.goal_env goal in
                  split_env bv uu___4 in
                match uu___3 with
                | FStar_Pervasives_Native.None ->
                    FStar_Tactics_Monad.fail
                      "binder not found in environment"
                | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                    let uu___4 = destruct_eq e0 bv1.FStar_Syntax_Syntax.sort in
                    (match uu___4 with
                     | FStar_Pervasives_Native.Some (x, e) ->
                         let uu___5 =
                           let uu___6 = FStar_Syntax_Subst.compress x in
                           uu___6.FStar_Syntax_Syntax.n in
                         (match uu___5 with
                          | FStar_Syntax_Syntax.Tm_name x1 ->
                              let s = [FStar_Syntax_Syntax.NT (x1, e)] in
                              let t = FStar_Tactics_Types.goal_type goal in
                              let bs =
                                FStar_Compiler_List.map
                                  FStar_Syntax_Syntax.mk_binder bvs in
                              let uu___6 =
                                let uu___7 =
                                  FStar_Syntax_Subst.close_binders bs in
                                let uu___8 = FStar_Syntax_Subst.close bs t in
                                (uu___7, uu___8) in
                              (match uu___6 with
                               | (bs', t') ->
                                   let uu___7 =
                                     let uu___8 =
                                       FStar_Syntax_Subst.subst_binders s bs' in
                                     let uu___9 =
                                       FStar_Syntax_Subst.subst s t' in
                                     (uu___8, uu___9) in
                                   (match uu___7 with
                                    | (bs'1, t'1) ->
                                        let e01 =
                                          FStar_TypeChecker_Env.push_bvs e0
                                            [bv1] in
                                        let uu___8 =
                                          FStar_TypeChecker_Core.open_binders_in_term
                                            e01 bs'1 t'1 in
                                        (match uu___8 with
                                         | (new_env, bs'', t'') ->
                                             let uu___9 =
                                               let uu___10 =
                                                 let uu___11 =
                                                   should_check_goal_uvar
                                                     goal in
                                                 FStar_Pervasives_Native.Some
                                                   uu___11 in
                                               let uu___11 =
                                                 goal_typedness_deps goal in
                                               FStar_Tactics_Monad.new_uvar
                                                 "rewrite" new_env t''
                                                 uu___10 uu___11
                                                 (rangeof goal) in
                                             FStar_Tactics_Monad.op_let_Bang
                                               uu___9
                                               (fun uu___10 ->
                                                  match uu___10 with
                                                  | (uvt, uv) ->
                                                      let goal' =
                                                        FStar_Tactics_Types.mk_goal
                                                          new_env uv
                                                          goal.FStar_Tactics_Types.opts
                                                          goal.FStar_Tactics_Types.is_guard
                                                          goal.FStar_Tactics_Types.label in
                                                      let sol =
                                                        let uu___11 =
                                                          FStar_Syntax_Util.abs
                                                            bs'' uvt
                                                            FStar_Pervasives_Native.None in
                                                        let uu___12 =
                                                          FStar_Compiler_List.map
                                                            (fun uu___13 ->
                                                               match uu___13
                                                               with
                                                               | {
                                                                   FStar_Syntax_Syntax.binder_bv
                                                                    = bv2;
                                                                   FStar_Syntax_Syntax.binder_qual
                                                                    = uu___14;
                                                                   FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___15;
                                                                   FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___16;_}
                                                                   ->
                                                                   let uu___17
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv2 in
                                                                   FStar_Syntax_Syntax.as_arg
                                                                    uu___17)
                                                            bs in
                                                        FStar_Syntax_Util.mk_app
                                                          uu___11 uu___12 in
                                                      let uu___11 =
                                                        set_solution goal sol in
                                                      FStar_Tactics_Monad.op_let_Bang
                                                        uu___11
                                                        (fun uu___12 ->
                                                           FStar_Tactics_Monad.replace_cur
                                                             goal')))))
                          | uu___6 ->
                              FStar_Tactics_Monad.fail
                                "Not an equality hypothesis with a variable on the LHS")
                     | uu___5 ->
                         FStar_Tactics_Monad.fail
                           "Not an equality hypothesis"))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "rewrite") uu___
let (rename_to :
  FStar_Syntax_Syntax.binder ->
    Prims.string -> FStar_Syntax_Syntax.binder FStar_Tactics_Monad.tac)
  =
  fun b ->
    fun s ->
      let uu___ =
        FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let bv = b.FStar_Syntax_Syntax.binder_bv in
             let bv' =
               let uu___1 =
                 let uu___2 =
                   let uu___3 =
                     let uu___4 =
                       FStar_Ident.range_of_id bv.FStar_Syntax_Syntax.ppname in
                     (s, uu___4) in
                   FStar_Ident.mk_ident uu___3 in
                 {
                   FStar_Syntax_Syntax.ppname = uu___2;
                   FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
                   FStar_Syntax_Syntax.sort = (bv.FStar_Syntax_Syntax.sort)
                 } in
               FStar_Syntax_Syntax.freshen_bv uu___1 in
             let uu___1 = subst_goal bv bv' goal in
             FStar_Tactics_Monad.op_let_Bang uu___1
               (fun uu___2 ->
                  match uu___2 with
                  | FStar_Pervasives_Native.None ->
                      FStar_Tactics_Monad.fail
                        "binder not found in environment"
                  | FStar_Pervasives_Native.Some (bv'1, goal1) ->
                      let uu___3 = FStar_Tactics_Monad.replace_cur goal1 in
                      FStar_Tactics_Monad.op_let_Bang uu___3
                        (fun uu___4 ->
                           FStar_Tactics_Monad.ret
                             {
                               FStar_Syntax_Syntax.binder_bv = bv'1;
                               FStar_Syntax_Syntax.binder_qual =
                                 (b.FStar_Syntax_Syntax.binder_qual);
                               FStar_Syntax_Syntax.binder_positivity =
                                 (b.FStar_Syntax_Syntax.binder_positivity);
                               FStar_Syntax_Syntax.binder_attrs =
                                 (b.FStar_Syntax_Syntax.binder_attrs)
                             }))) in
      FStar_Compiler_Effect.op_Less_Bar
        (FStar_Tactics_Monad.wrap_err "rename_to") uu___
let (binder_retype :
  FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let uu___ =
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let bv = b.FStar_Syntax_Syntax.binder_bv in
           let uu___1 =
             let uu___2 = FStar_Tactics_Types.goal_env goal in
             split_env bv uu___2 in
           match uu___1 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail
                 "binder is not present in environment"
           | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
               let uu___2 = FStar_Syntax_Util.type_u () in
               (match uu___2 with
                | (ty, u) ->
                    let goal_sc = should_check_goal_uvar goal in
                    let uu___3 =
                      let uu___4 = goal_typedness_deps goal in
                      FStar_Tactics_Monad.new_uvar "binder_retype" e0 ty
                        (FStar_Pervasives_Native.Some goal_sc) uu___4
                        (rangeof goal) in
                    FStar_Tactics_Monad.op_let_Bang uu___3
                      (fun uu___4 ->
                         match uu___4 with
                         | (t', u_t') ->
                             let bv'' =
                               {
                                 FStar_Syntax_Syntax.ppname =
                                   (bv1.FStar_Syntax_Syntax.ppname);
                                 FStar_Syntax_Syntax.index =
                                   (bv1.FStar_Syntax_Syntax.index);
                                 FStar_Syntax_Syntax.sort = t'
                               } in
                             let s =
                               let uu___5 =
                                 let uu___6 =
                                   let uu___7 =
                                     FStar_Syntax_Syntax.bv_to_name bv'' in
                                   (bv1, uu___7) in
                                 FStar_Syntax_Syntax.NT uu___6 in
                               [uu___5] in
                             let bvs1 =
                               FStar_Compiler_List.map
                                 (fun b1 ->
                                    let uu___5 =
                                      FStar_Syntax_Subst.subst s
                                        b1.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (b1.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (b1.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu___5
                                    }) bvs in
                             let env' =
                               FStar_TypeChecker_Env.push_bvs e0 (bv'' ::
                                 bvs1) in
                             FStar_Tactics_Monad.op_let_Bang
                               FStar_Tactics_Monad.dismiss
                               (fun uu___5 ->
                                  let new_goal =
                                    let uu___6 =
                                      FStar_Tactics_Types.goal_with_env goal
                                        env' in
                                    let uu___7 =
                                      let uu___8 =
                                        FStar_Tactics_Types.goal_type goal in
                                      FStar_Syntax_Subst.subst s uu___8 in
                                    goal_with_type uu___6 uu___7 in
                                  let uu___6 =
                                    FStar_Tactics_Monad.add_goals [new_goal] in
                                  FStar_Tactics_Monad.op_let_Bang uu___6
                                    (fun uu___7 ->
                                       let uu___8 =
                                         FStar_Syntax_Util.mk_eq2
                                           (FStar_Syntax_Syntax.U_succ u) ty
                                           bv1.FStar_Syntax_Syntax.sort t' in
                                       FStar_Tactics_Monad.add_irrelevant_goal
                                         goal "binder_retype equation" e0
                                         uu___8
                                         (FStar_Pervasives_Native.Some
                                            goal_sc)))))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "binder_retype") uu___
let (norm_binder_type :
  FStar_Pervasives.norm_step Prims.list ->
    FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac)
  =
  fun s ->
    fun b ->
      let uu___ =
        FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
          (fun goal ->
             let bv = b.FStar_Syntax_Syntax.binder_bv in
             let uu___1 =
               let uu___2 = FStar_Tactics_Types.goal_env goal in
               split_env bv uu___2 in
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail
                   "binder is not present in environment"
             | FStar_Pervasives_Native.Some (e0, bv1, bvs) ->
                 let steps =
                   let uu___2 = FStar_TypeChecker_Cfg.translate_norm_steps s in
                   FStar_Compiler_List.op_At
                     [FStar_TypeChecker_Env.Reify;
                     FStar_TypeChecker_Env.UnfoldTac] uu___2 in
                 let sort' = normalize steps e0 bv1.FStar_Syntax_Syntax.sort in
                 let bv' =
                   {
                     FStar_Syntax_Syntax.ppname =
                       (bv1.FStar_Syntax_Syntax.ppname);
                     FStar_Syntax_Syntax.index =
                       (bv1.FStar_Syntax_Syntax.index);
                     FStar_Syntax_Syntax.sort = sort'
                   } in
                 let env' = FStar_TypeChecker_Env.push_bvs e0 (bv' :: bvs) in
                 let uu___2 = FStar_Tactics_Types.goal_with_env goal env' in
                 FStar_Tactics_Monad.replace_cur uu___2) in
      FStar_Compiler_Effect.op_Less_Bar
        (FStar_Tactics_Monad.wrap_err "norm_binder_type") uu___
let (revert : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu___1 =
           let uu___2 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu___2 in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot revert; empty context"
         | FStar_Pervasives_Native.Some (x, env') ->
             let typ' =
               let uu___2 =
                 let uu___3 = FStar_Syntax_Syntax.mk_binder x in [uu___3] in
               let uu___3 =
                 let uu___4 = FStar_Tactics_Types.goal_type goal in
                 FStar_Syntax_Syntax.mk_Total uu___4 in
               FStar_Syntax_Util.arrow uu___2 uu___3 in
             let uu___2 =
               let uu___3 =
                 let uu___4 = should_check_goal_uvar goal in
                 FStar_Pervasives_Native.Some uu___4 in
               let uu___4 = goal_typedness_deps goal in
               FStar_Tactics_Monad.new_uvar "revert" env' typ' uu___3 uu___4
                 (rangeof goal) in
             FStar_Tactics_Monad.op_let_Bang uu___2
               (fun uu___3 ->
                  match uu___3 with
                  | (r, u_r) ->
                      let uu___4 =
                        let uu___5 =
                          let uu___6 =
                            let uu___7 =
                              let uu___8 = FStar_Syntax_Syntax.bv_to_name x in
                              FStar_Syntax_Syntax.as_arg uu___8 in
                            [uu___7] in
                          let uu___7 =
                            let uu___8 = FStar_Tactics_Types.goal_type goal in
                            uu___8.FStar_Syntax_Syntax.pos in
                          FStar_Syntax_Syntax.mk_Tm_app r uu___6 uu___7 in
                        set_solution goal uu___5 in
                      FStar_Tactics_Monad.op_let_Bang uu___4
                        (fun uu___5 ->
                           let g =
                             FStar_Tactics_Types.mk_goal env' u_r
                               goal.FStar_Tactics_Types.opts
                               goal.FStar_Tactics_Types.is_guard
                               goal.FStar_Tactics_Types.label in
                           FStar_Tactics_Monad.replace_cur g)))
let (free_in :
  FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun bv ->
    fun t ->
      let uu___ = FStar_Syntax_Free.names t in
      FStar_Compiler_Util.set_mem bv uu___
let (clear : FStar_Syntax_Syntax.binder -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    let bv = b.FStar_Syntax_Syntax.binder_bv in
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu___ =
           FStar_Tactics_Monad.if_verbose
             (fun uu___1 ->
                let uu___2 = FStar_Syntax_Print.binder_to_string b in
                let uu___3 =
                  let uu___4 =
                    let uu___5 =
                      let uu___6 = FStar_Tactics_Types.goal_env goal in
                      FStar_TypeChecker_Env.all_binders uu___6 in
                    FStar_Compiler_Effect.op_Bar_Greater uu___5
                      FStar_Compiler_List.length in
                  FStar_Compiler_Effect.op_Bar_Greater uu___4
                    FStar_Compiler_Util.string_of_int in
                FStar_Compiler_Util.print2
                  "Clear of (%s), env has %s binders\n" uu___2 uu___3) in
         FStar_Tactics_Monad.op_let_Bang uu___
           (fun uu___1 ->
              let uu___2 =
                let uu___3 = FStar_Tactics_Types.goal_env goal in
                split_env bv uu___3 in
              match uu___2 with
              | FStar_Pervasives_Native.None ->
                  FStar_Tactics_Monad.fail
                    "Cannot clear; binder not in environment"
              | FStar_Pervasives_Native.Some (e', bv1, bvs) ->
                  let rec check bvs1 =
                    match bvs1 with
                    | [] -> FStar_Tactics_Monad.ret ()
                    | bv'::bvs2 ->
                        let uu___3 = free_in bv1 bv'.FStar_Syntax_Syntax.sort in
                        if uu___3
                        then
                          let uu___4 =
                            let uu___5 = FStar_Syntax_Print.bv_to_string bv' in
                            FStar_Compiler_Util.format1
                              "Cannot clear; binder present in the type of %s"
                              uu___5 in
                          FStar_Tactics_Monad.fail uu___4
                        else check bvs2 in
                  let uu___3 =
                    let uu___4 = FStar_Tactics_Types.goal_type goal in
                    free_in bv1 uu___4 in
                  if uu___3
                  then
                    FStar_Tactics_Monad.fail
                      "Cannot clear; binder present in goal"
                  else
                    (let uu___5 = check bvs in
                     FStar_Tactics_Monad.op_let_Bang uu___5
                       (fun uu___6 ->
                          let env' = FStar_TypeChecker_Env.push_bvs e' bvs in
                          let uu___7 =
                            let uu___8 = FStar_Tactics_Types.goal_type goal in
                            let uu___9 =
                              let uu___10 = should_check_goal_uvar goal in
                              FStar_Pervasives_Native.Some uu___10 in
                            let uu___10 = goal_typedness_deps goal in
                            FStar_Tactics_Monad.new_uvar "clear.witness" env'
                              uu___8 uu___9 uu___10 (rangeof goal) in
                          FStar_Tactics_Monad.op_let_Bang uu___7
                            (fun uu___8 ->
                               match uu___8 with
                               | (ut, uvar_ut) ->
                                   let uu___9 = set_solution goal ut in
                                   FStar_Tactics_Monad.op_let_Bang uu___9
                                     (fun uu___10 ->
                                        let uu___11 =
                                          FStar_Tactics_Types.mk_goal env'
                                            uvar_ut
                                            goal.FStar_Tactics_Types.opts
                                            goal.FStar_Tactics_Types.is_guard
                                            goal.FStar_Tactics_Types.label in
                                        FStar_Tactics_Monad.replace_cur
                                          uu___11))))))
let (clear_top : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun goal ->
         let uu___1 =
           let uu___2 = FStar_Tactics_Types.goal_env goal in
           FStar_TypeChecker_Env.pop_bv uu___2 in
         match uu___1 with
         | FStar_Pervasives_Native.None ->
             FStar_Tactics_Monad.fail "Cannot clear; empty context"
         | FStar_Pervasives_Native.Some (x, uu___2) ->
             let uu___3 = FStar_Syntax_Syntax.mk_binder x in clear uu___3)
let (prune : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu___ = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.rem_proof_ns ctx uu___ in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (addns : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun g ->
         let ctx = FStar_Tactics_Types.goal_env g in
         let ctx' =
           let uu___ = FStar_Ident.path_of_text s in
           FStar_TypeChecker_Env.add_proof_ns ctx uu___ in
         let g' = FStar_Tactics_Types.goal_with_env g ctx' in
         FStar_Tactics_Monad.replace_cur g')
let (guard_formula :
  FStar_TypeChecker_Common.guard_t -> FStar_Syntax_Syntax.term) =
  fun g ->
    match g.FStar_TypeChecker_Common.guard_f with
    | FStar_TypeChecker_Common.Trivial -> FStar_Syntax_Util.t_true
    | FStar_TypeChecker_Common.NonTrivial f -> f
let (_t_trefl :
  Prims.bool ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun allow_guards ->
    fun l ->
      fun r ->
        let should_register_trefl g =
          let should_register = true in
          let skip_register = false in
          let uu___ =
            let uu___1 = FStar_Options.compat_pre_core_should_register () in
            Prims.op_Negation uu___1 in
          if uu___
          then skip_register
          else
            (let is_uvar_untyped_or_already_checked u =
               let dec =
                 FStar_Syntax_Unionfind.find_decoration
                   u.FStar_Syntax_Syntax.ctx_uvar_head in
               match dec.FStar_Syntax_Syntax.uvar_decoration_should_check
               with
               | FStar_Syntax_Syntax.Allow_untyped uu___2 -> true
               | FStar_Syntax_Syntax.Already_checked -> true
               | uu___2 -> false in
             let is_uvar t =
               let head = FStar_Syntax_Util.leftmost_head t in
               let uu___2 =
                 let uu___3 = FStar_Syntax_Subst.compress head in
                 uu___3.FStar_Syntax_Syntax.n in
               match uu___2 with
               | FStar_Syntax_Syntax.Tm_uvar (u, uu___3) ->
                   FStar_Pervasives.Inl (u, head, t)
               | uu___3 -> FStar_Pervasives.Inr t in
             let is_allow_untyped_uvar t =
               let uu___2 = is_uvar t in
               match uu___2 with
               | FStar_Pervasives.Inr uu___3 -> false
               | FStar_Pervasives.Inl (u, uu___3, uu___4) ->
                   is_uvar_untyped_or_already_checked u in
             let t =
               FStar_Syntax_Util.ctx_uvar_typ
                 g.FStar_Tactics_Types.goal_ctx_uvar in
             let uvars =
               let uu___2 = FStar_Syntax_Free.uvars t in
               FStar_Compiler_Util.set_elements uu___2 in
             let uu___2 =
               FStar_Compiler_Util.for_all is_uvar_untyped_or_already_checked
                 uvars in
             if uu___2
             then skip_register
             else
               (let uu___4 =
                  let t1 =
                    let uu___5 = FStar_Syntax_Util.un_squash t in
                    match uu___5 with
                    | FStar_Pervasives_Native.None -> t
                    | FStar_Pervasives_Native.Some t2 -> t2 in
                  FStar_Syntax_Util.leftmost_head_and_args t1 in
                match uu___4 with
                | (head, args) ->
                    let uu___5 =
                      let uu___6 =
                        let uu___7 =
                          let uu___8 = FStar_Syntax_Util.un_uinst head in
                          FStar_Syntax_Subst.compress uu___8 in
                        uu___7.FStar_Syntax_Syntax.n in
                      (uu___6, args) in
                    (match uu___5 with
                     | (FStar_Syntax_Syntax.Tm_fvar fv,
                        (ty, uu___6)::(t1, uu___7)::(t2, uu___8)::[]) when
                         FStar_Syntax_Syntax.fv_eq_lid fv
                           FStar_Parser_Const.eq2_lid
                         ->
                         let uu___9 =
                           (is_allow_untyped_uvar t1) ||
                             (is_allow_untyped_uvar t2) in
                         if uu___9
                         then skip_register
                         else
                           (let uu___11 =
                              FStar_Tactics_Monad.is_goal_safe_as_well_typed
                                g in
                            if uu___11
                            then
                              let check_uvar_subtype u t3 =
                                let env1 =
                                  let uu___12 =
                                    FStar_Tactics_Types.goal_env g in
                                  {
                                    FStar_TypeChecker_Env.solver =
                                      (uu___12.FStar_TypeChecker_Env.solver);
                                    FStar_TypeChecker_Env.range =
                                      (uu___12.FStar_TypeChecker_Env.range);
                                    FStar_TypeChecker_Env.curmodule =
                                      (uu___12.FStar_TypeChecker_Env.curmodule);
                                    FStar_TypeChecker_Env.gamma =
                                      ((g.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma);
                                    FStar_TypeChecker_Env.gamma_sig =
                                      (uu___12.FStar_TypeChecker_Env.gamma_sig);
                                    FStar_TypeChecker_Env.gamma_cache =
                                      (uu___12.FStar_TypeChecker_Env.gamma_cache);
                                    FStar_TypeChecker_Env.modules =
                                      (uu___12.FStar_TypeChecker_Env.modules);
                                    FStar_TypeChecker_Env.expected_typ =
                                      (uu___12.FStar_TypeChecker_Env.expected_typ);
                                    FStar_TypeChecker_Env.sigtab =
                                      (uu___12.FStar_TypeChecker_Env.sigtab);
                                    FStar_TypeChecker_Env.attrtab =
                                      (uu___12.FStar_TypeChecker_Env.attrtab);
                                    FStar_TypeChecker_Env.instantiate_imp =
                                      (uu___12.FStar_TypeChecker_Env.instantiate_imp);
                                    FStar_TypeChecker_Env.effects =
                                      (uu___12.FStar_TypeChecker_Env.effects);
                                    FStar_TypeChecker_Env.generalize =
                                      (uu___12.FStar_TypeChecker_Env.generalize);
                                    FStar_TypeChecker_Env.letrecs =
                                      (uu___12.FStar_TypeChecker_Env.letrecs);
                                    FStar_TypeChecker_Env.top_level =
                                      (uu___12.FStar_TypeChecker_Env.top_level);
                                    FStar_TypeChecker_Env.check_uvars =
                                      (uu___12.FStar_TypeChecker_Env.check_uvars);
                                    FStar_TypeChecker_Env.use_eq_strict =
                                      (uu___12.FStar_TypeChecker_Env.use_eq_strict);
                                    FStar_TypeChecker_Env.is_iface =
                                      (uu___12.FStar_TypeChecker_Env.is_iface);
                                    FStar_TypeChecker_Env.admit =
                                      (uu___12.FStar_TypeChecker_Env.admit);
                                    FStar_TypeChecker_Env.lax =
                                      (uu___12.FStar_TypeChecker_Env.lax);
                                    FStar_TypeChecker_Env.lax_universes =
                                      (uu___12.FStar_TypeChecker_Env.lax_universes);
                                    FStar_TypeChecker_Env.phase1 =
                                      (uu___12.FStar_TypeChecker_Env.phase1);
                                    FStar_TypeChecker_Env.failhard =
                                      (uu___12.FStar_TypeChecker_Env.failhard);
                                    FStar_TypeChecker_Env.nosynth =
                                      (uu___12.FStar_TypeChecker_Env.nosynth);
                                    FStar_TypeChecker_Env.uvar_subtyping =
                                      (uu___12.FStar_TypeChecker_Env.uvar_subtyping);
                                    FStar_TypeChecker_Env.intactics =
                                      (uu___12.FStar_TypeChecker_Env.intactics);
                                    FStar_TypeChecker_Env.nocoerce =
                                      (uu___12.FStar_TypeChecker_Env.nocoerce);
                                    FStar_TypeChecker_Env.tc_term =
                                      (uu___12.FStar_TypeChecker_Env.tc_term);
                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                      =
                                      (uu___12.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.universe_of =
                                      (uu___12.FStar_TypeChecker_Env.universe_of);
                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                      =
                                      (uu___12.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                    FStar_TypeChecker_Env.teq_nosmt_force =
                                      (uu___12.FStar_TypeChecker_Env.teq_nosmt_force);
                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                      =
                                      (uu___12.FStar_TypeChecker_Env.subtype_nosmt_force);
                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                      =
                                      (uu___12.FStar_TypeChecker_Env.qtbl_name_and_index);
                                    FStar_TypeChecker_Env.normalized_eff_names
                                      =
                                      (uu___12.FStar_TypeChecker_Env.normalized_eff_names);
                                    FStar_TypeChecker_Env.fv_delta_depths =
                                      (uu___12.FStar_TypeChecker_Env.fv_delta_depths);
                                    FStar_TypeChecker_Env.proof_ns =
                                      (uu___12.FStar_TypeChecker_Env.proof_ns);
                                    FStar_TypeChecker_Env.synth_hook =
                                      (uu___12.FStar_TypeChecker_Env.synth_hook);
                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                      =
                                      (uu___12.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                    FStar_TypeChecker_Env.splice =
                                      (uu___12.FStar_TypeChecker_Env.splice);
                                    FStar_TypeChecker_Env.mpreprocess =
                                      (uu___12.FStar_TypeChecker_Env.mpreprocess);
                                    FStar_TypeChecker_Env.postprocess =
                                      (uu___12.FStar_TypeChecker_Env.postprocess);
                                    FStar_TypeChecker_Env.identifier_info =
                                      (uu___12.FStar_TypeChecker_Env.identifier_info);
                                    FStar_TypeChecker_Env.tc_hooks =
                                      (uu___12.FStar_TypeChecker_Env.tc_hooks);
                                    FStar_TypeChecker_Env.dsenv =
                                      (uu___12.FStar_TypeChecker_Env.dsenv);
                                    FStar_TypeChecker_Env.nbe =
                                      (uu___12.FStar_TypeChecker_Env.nbe);
                                    FStar_TypeChecker_Env.strict_args_tab =
                                      (uu___12.FStar_TypeChecker_Env.strict_args_tab);
                                    FStar_TypeChecker_Env.erasable_types_tab
                                      =
                                      (uu___12.FStar_TypeChecker_Env.erasable_types_tab);
                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                      =
                                      (uu___12.FStar_TypeChecker_Env.enable_defer_to_tac);
                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                      =
                                      (uu___12.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                    FStar_TypeChecker_Env.erase_erasable_args
                                      =
                                      (uu___12.FStar_TypeChecker_Env.erase_erasable_args);
                                    FStar_TypeChecker_Env.core_check =
                                      (uu___12.FStar_TypeChecker_Env.core_check)
                                  } in
                                let uu___12 =
                                  FStar_TypeChecker_Core.compute_term_type_handle_guards
                                    env1 t3
                                    (fun uu___13 -> fun uu___14 -> true) in
                                match uu___12 with
                                | FStar_Pervasives.Inr uu___13 -> false
                                | FStar_Pervasives.Inl (uu___13, t_ty) ->
                                    let uu___14 =
                                      FStar_TypeChecker_Core.check_term_subtyping
                                        env1 ty t_ty in
                                    (match uu___14 with
                                     | FStar_Pervasives.Inl
                                         (FStar_Pervasives_Native.None) ->
                                         (mark_uvar_as_already_checked u;
                                          true)
                                     | uu___15 -> false) in
                              let uu___12 =
                                let uu___13 = is_uvar t1 in
                                let uu___14 = is_uvar t2 in
                                (uu___13, uu___14) in
                              match uu___12 with
                              | (FStar_Pervasives.Inl (u, uu___13, tu),
                                 FStar_Pervasives.Inr uu___14) ->
                                  let uu___15 = check_uvar_subtype u tu in
                                  (if uu___15
                                   then skip_register
                                   else should_register)
                              | (FStar_Pervasives.Inr uu___13,
                                 FStar_Pervasives.Inl (u, uu___14, tu)) ->
                                  let uu___15 = check_uvar_subtype u tu in
                                  (if uu___15
                                   then skip_register
                                   else should_register)
                              | uu___13 -> should_register
                            else should_register)
                     | uu___6 -> should_register))) in
        FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
          (fun g ->
             let should_check = should_check_goal_uvar g in
             (let uu___1 = should_register_trefl g in
              if uu___1 then FStar_Tactics_Monad.register_goal g else ());
             (let must_tot = true in
              let attempt l1 r1 =
                let uu___1 =
                  let uu___2 = FStar_Tactics_Types.goal_env g in
                  do_unify_maybe_guards allow_guards must_tot uu___2 l1 r1 in
                FStar_Tactics_Monad.op_let_Bang uu___1
                  (fun uu___2 ->
                     match uu___2 with
                     | FStar_Pervasives_Native.None ->
                         FStar_Tactics_Monad.ret false
                     | FStar_Pervasives_Native.Some guard ->
                         let uu___3 = solve' g FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.op_let_Bang uu___3
                           (fun uu___4 ->
                              if allow_guards
                              then
                                let uu___5 =
                                  let uu___6 = FStar_Tactics_Types.goal_env g in
                                  let uu___7 = guard_formula guard in
                                  FStar_Tactics_Monad.goal_of_guard "t_trefl"
                                    uu___6 uu___7
                                    (FStar_Pervasives_Native.Some
                                       should_check) (rangeof g) in
                                FStar_Tactics_Monad.op_let_Bang uu___5
                                  (fun goal ->
                                     let uu___6 =
                                       FStar_Tactics_Monad.push_goals [goal] in
                                     FStar_Tactics_Monad.op_let_Bang uu___6
                                       (fun uu___7 ->
                                          FStar_Tactics_Monad.ret true))
                              else
                                (let uu___6 =
                                   FStar_TypeChecker_Env.is_trivial_guard_formula
                                     guard in
                                 if uu___6
                                 then FStar_Tactics_Monad.ret true
                                 else
                                   failwith
                                     "internal error: _t_refl: guard is not trivial"))) in
              let uu___1 = attempt l r in
              FStar_Tactics_Monad.op_let_Bang uu___1
                (fun uu___2 ->
                   if uu___2
                   then FStar_Tactics_Monad.ret ()
                   else
                     (let norm1 =
                        let uu___3 = FStar_Tactics_Types.goal_env g in
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Env.UnfoldUntil
                             FStar_Syntax_Syntax.delta_constant;
                          FStar_TypeChecker_Env.Primops;
                          FStar_TypeChecker_Env.UnfoldTac] uu___3 in
                      let uu___3 =
                        let uu___4 = norm1 l in
                        let uu___5 = norm1 r in attempt uu___4 uu___5 in
                      FStar_Tactics_Monad.op_let_Bang uu___3
                        (fun uu___4 ->
                           if uu___4
                           then FStar_Tactics_Monad.ret ()
                           else
                             (let uu___5 =
                                let uu___6 =
                                  let uu___7 = FStar_Tactics_Types.goal_env g in
                                  tts uu___7 in
                                FStar_TypeChecker_Err.print_discrepancy
                                  uu___6 l r in
                              match uu___5 with
                              | (ls, rs) ->
                                  fail2 "cannot unify (%s) and (%s)" ls rs))))))
let (t_trefl : Prims.bool -> unit FStar_Tactics_Monad.tac) =
  fun allow_guards ->
    let uu___ =
      let uu___1 =
        let uu___2 =
          FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
            (fun g ->
               let uu___3 =
                 let uu___4 = FStar_Tactics_Types.goal_env g in
                 let uu___5 = FStar_Tactics_Types.goal_type g in
                 destruct_eq uu___4 uu___5 in
               match uu___3 with
               | FStar_Pervasives_Native.Some (l, r) ->
                   _t_trefl allow_guards l r
               | FStar_Pervasives_Native.None ->
                   let uu___4 =
                     let uu___5 = FStar_Tactics_Types.goal_env g in
                     let uu___6 = FStar_Tactics_Types.goal_type g in
                     tts uu___5 uu___6 in
                   fail1 "not an equality (%s)" uu___4) in
        FStar_Tactics_Monad.catch uu___2 in
      FStar_Tactics_Monad.op_let_Bang uu___1
        (fun uu___2 ->
           match uu___2 with
           | FStar_Pervasives.Inr v -> FStar_Tactics_Monad.ret ()
           | FStar_Pervasives.Inl exn -> FStar_Tactics_Monad.traise exn) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "t_trefl") uu___
let (dup : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun g ->
         let goal_sc = should_check_goal_uvar g in
         let env1 = FStar_Tactics_Types.goal_env g in
         let uu___1 =
           let uu___2 = FStar_Tactics_Types.goal_type g in
           let uu___3 =
             let uu___4 = should_check_goal_uvar g in
             FStar_Pervasives_Native.Some uu___4 in
           let uu___4 = goal_typedness_deps g in
           FStar_Tactics_Monad.new_uvar "dup" env1 uu___2 uu___3 uu___4
             (rangeof g) in
         FStar_Tactics_Monad.op_let_Bang uu___1
           (fun uu___2 ->
              match uu___2 with
              | (u, u_uvar) ->
                  (mark_uvar_as_already_checked
                     g.FStar_Tactics_Types.goal_ctx_uvar;
                   (let g' =
                      {
                        FStar_Tactics_Types.goal_main_env =
                          (g.FStar_Tactics_Types.goal_main_env);
                        FStar_Tactics_Types.goal_ctx_uvar = u_uvar;
                        FStar_Tactics_Types.opts =
                          (g.FStar_Tactics_Types.opts);
                        FStar_Tactics_Types.is_guard =
                          (g.FStar_Tactics_Types.is_guard);
                        FStar_Tactics_Types.label =
                          (g.FStar_Tactics_Types.label)
                      } in
                    FStar_Tactics_Monad.op_let_Bang
                      FStar_Tactics_Monad.dismiss
                      (fun uu___4 ->
                         let t_eq =
                           let uu___5 =
                             let uu___6 = FStar_Tactics_Types.goal_type g in
                             env1.FStar_TypeChecker_Env.universe_of env1
                               uu___6 in
                           let uu___6 = FStar_Tactics_Types.goal_type g in
                           let uu___7 = FStar_Tactics_Types.goal_witness g in
                           FStar_Syntax_Util.mk_eq2 uu___5 uu___6 u uu___7 in
                         let uu___5 =
                           FStar_Tactics_Monad.add_irrelevant_goal g
                             "dup equation" env1 t_eq
                             (FStar_Pervasives_Native.Some goal_sc) in
                         FStar_Tactics_Monad.op_let_Bang uu___5
                           (fun uu___6 -> FStar_Tactics_Monad.add_goals [g']))))))
let longest_prefix :
  'a .
    ('a -> 'a -> Prims.bool) ->
      'a Prims.list ->
        'a Prims.list -> ('a Prims.list * 'a Prims.list * 'a Prims.list)
  =
  fun f ->
    fun l1 ->
      fun l2 ->
        let rec aux acc l11 l21 =
          match (l11, l21) with
          | (x::xs, y::ys) ->
              let uu___ = f x y in
              if uu___
              then aux (x :: acc) xs ys
              else (acc, (x :: xs), (y :: ys))
          | uu___ -> (acc, l11, l21) in
        let uu___ = aux [] l1 l2 in
        match uu___ with
        | (pr, t1, t2) -> ((FStar_Compiler_List.rev pr), t1, t2)
let (eq_binding :
  FStar_Syntax_Syntax.binding -> FStar_Syntax_Syntax.binding -> Prims.bool) =
  fun b1 ->
    fun b2 ->
      match (b1, b2) with
      | (FStar_Syntax_Syntax.Binding_var bv1, FStar_Syntax_Syntax.Binding_var
         bv2) ->
          (FStar_Syntax_Syntax.bv_eq bv1 bv2) &&
            (FStar_Syntax_Util.term_eq bv1.FStar_Syntax_Syntax.sort
               bv2.FStar_Syntax_Syntax.sort)
      | (FStar_Syntax_Syntax.Binding_lid (lid1, uu___),
         FStar_Syntax_Syntax.Binding_lid (lid2, uu___1)) ->
          FStar_Ident.lid_equals lid1 lid2
      | (FStar_Syntax_Syntax.Binding_univ u1,
         FStar_Syntax_Syntax.Binding_univ u2) ->
          FStar_Ident.ident_equals u1 u2
      | uu___ -> false
let (join_goals :
  FStar_Tactics_Types.goal ->
    FStar_Tactics_Types.goal ->
      FStar_Tactics_Types.goal FStar_Tactics_Monad.tac)
  =
  fun g1 ->
    fun g2 ->
      let close_forall_no_univs bs f =
        FStar_Compiler_List.fold_right
          (fun b ->
             fun f1 ->
               FStar_Syntax_Util.mk_forall_no_univ
                 b.FStar_Syntax_Syntax.binder_bv f1) bs f in
      let uu___ = FStar_Tactics_Types.get_phi g1 in
      match uu___ with
      | FStar_Pervasives_Native.None ->
          FStar_Tactics_Monad.fail "goal 1 is not irrelevant"
      | FStar_Pervasives_Native.Some phi1 ->
          let uu___1 = FStar_Tactics_Types.get_phi g2 in
          (match uu___1 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "goal 2 is not irrelevant"
           | FStar_Pervasives_Native.Some phi2 ->
               let gamma1 =
                 (g1.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let gamma2 =
                 (g2.FStar_Tactics_Types.goal_ctx_uvar).FStar_Syntax_Syntax.ctx_uvar_gamma in
               let uu___2 =
                 longest_prefix eq_binding (FStar_Compiler_List.rev gamma1)
                   (FStar_Compiler_List.rev gamma2) in
               (match uu___2 with
                | (gamma, r1, r2) ->
                    let t1 =
                      let uu___3 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_Compiler_List.rev r1) in
                      close_forall_no_univs uu___3 phi1 in
                    let t2 =
                      let uu___3 =
                        FStar_TypeChecker_Env.binders_of_bindings
                          (FStar_Compiler_List.rev r2) in
                      close_forall_no_univs uu___3 phi2 in
                    let goal_sc =
                      let uu___3 =
                        let uu___4 = should_check_goal_uvar g1 in
                        let uu___5 = should_check_goal_uvar g2 in
                        (uu___4, uu___5) in
                      match uu___3 with
                      | (FStar_Syntax_Syntax.Allow_untyped reason1,
                         FStar_Syntax_Syntax.Allow_untyped uu___4) ->
                          FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.Allow_untyped reason1)
                      | uu___4 -> FStar_Pervasives_Native.None in
                    let uu___3 = set_solution g1 FStar_Syntax_Util.exp_unit in
                    FStar_Tactics_Monad.op_let_Bang uu___3
                      (fun uu___4 ->
                         let uu___5 =
                           set_solution g2 FStar_Syntax_Util.exp_unit in
                         FStar_Tactics_Monad.op_let_Bang uu___5
                           (fun uu___6 ->
                              let ng = FStar_Syntax_Util.mk_conj t1 t2 in
                              let nenv =
                                let uu___7 = FStar_Tactics_Types.goal_env g1 in
                                {
                                  FStar_TypeChecker_Env.solver =
                                    (uu___7.FStar_TypeChecker_Env.solver);
                                  FStar_TypeChecker_Env.range =
                                    (uu___7.FStar_TypeChecker_Env.range);
                                  FStar_TypeChecker_Env.curmodule =
                                    (uu___7.FStar_TypeChecker_Env.curmodule);
                                  FStar_TypeChecker_Env.gamma =
                                    (FStar_Compiler_List.rev gamma);
                                  FStar_TypeChecker_Env.gamma_sig =
                                    (uu___7.FStar_TypeChecker_Env.gamma_sig);
                                  FStar_TypeChecker_Env.gamma_cache =
                                    (uu___7.FStar_TypeChecker_Env.gamma_cache);
                                  FStar_TypeChecker_Env.modules =
                                    (uu___7.FStar_TypeChecker_Env.modules);
                                  FStar_TypeChecker_Env.expected_typ =
                                    (uu___7.FStar_TypeChecker_Env.expected_typ);
                                  FStar_TypeChecker_Env.sigtab =
                                    (uu___7.FStar_TypeChecker_Env.sigtab);
                                  FStar_TypeChecker_Env.attrtab =
                                    (uu___7.FStar_TypeChecker_Env.attrtab);
                                  FStar_TypeChecker_Env.instantiate_imp =
                                    (uu___7.FStar_TypeChecker_Env.instantiate_imp);
                                  FStar_TypeChecker_Env.effects =
                                    (uu___7.FStar_TypeChecker_Env.effects);
                                  FStar_TypeChecker_Env.generalize =
                                    (uu___7.FStar_TypeChecker_Env.generalize);
                                  FStar_TypeChecker_Env.letrecs =
                                    (uu___7.FStar_TypeChecker_Env.letrecs);
                                  FStar_TypeChecker_Env.top_level =
                                    (uu___7.FStar_TypeChecker_Env.top_level);
                                  FStar_TypeChecker_Env.check_uvars =
                                    (uu___7.FStar_TypeChecker_Env.check_uvars);
                                  FStar_TypeChecker_Env.use_eq_strict =
                                    (uu___7.FStar_TypeChecker_Env.use_eq_strict);
                                  FStar_TypeChecker_Env.is_iface =
                                    (uu___7.FStar_TypeChecker_Env.is_iface);
                                  FStar_TypeChecker_Env.admit =
                                    (uu___7.FStar_TypeChecker_Env.admit);
                                  FStar_TypeChecker_Env.lax =
                                    (uu___7.FStar_TypeChecker_Env.lax);
                                  FStar_TypeChecker_Env.lax_universes =
                                    (uu___7.FStar_TypeChecker_Env.lax_universes);
                                  FStar_TypeChecker_Env.phase1 =
                                    (uu___7.FStar_TypeChecker_Env.phase1);
                                  FStar_TypeChecker_Env.failhard =
                                    (uu___7.FStar_TypeChecker_Env.failhard);
                                  FStar_TypeChecker_Env.nosynth =
                                    (uu___7.FStar_TypeChecker_Env.nosynth);
                                  FStar_TypeChecker_Env.uvar_subtyping =
                                    (uu___7.FStar_TypeChecker_Env.uvar_subtyping);
                                  FStar_TypeChecker_Env.intactics =
                                    (uu___7.FStar_TypeChecker_Env.intactics);
                                  FStar_TypeChecker_Env.nocoerce =
                                    (uu___7.FStar_TypeChecker_Env.nocoerce);
                                  FStar_TypeChecker_Env.tc_term =
                                    (uu___7.FStar_TypeChecker_Env.tc_term);
                                  FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                    =
                                    (uu___7.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.universe_of =
                                    (uu___7.FStar_TypeChecker_Env.universe_of);
                                  FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                    =
                                    (uu___7.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                  FStar_TypeChecker_Env.teq_nosmt_force =
                                    (uu___7.FStar_TypeChecker_Env.teq_nosmt_force);
                                  FStar_TypeChecker_Env.subtype_nosmt_force =
                                    (uu___7.FStar_TypeChecker_Env.subtype_nosmt_force);
                                  FStar_TypeChecker_Env.qtbl_name_and_index =
                                    (uu___7.FStar_TypeChecker_Env.qtbl_name_and_index);
                                  FStar_TypeChecker_Env.normalized_eff_names
                                    =
                                    (uu___7.FStar_TypeChecker_Env.normalized_eff_names);
                                  FStar_TypeChecker_Env.fv_delta_depths =
                                    (uu___7.FStar_TypeChecker_Env.fv_delta_depths);
                                  FStar_TypeChecker_Env.proof_ns =
                                    (uu___7.FStar_TypeChecker_Env.proof_ns);
                                  FStar_TypeChecker_Env.synth_hook =
                                    (uu___7.FStar_TypeChecker_Env.synth_hook);
                                  FStar_TypeChecker_Env.try_solve_implicits_hook
                                    =
                                    (uu___7.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                  FStar_TypeChecker_Env.splice =
                                    (uu___7.FStar_TypeChecker_Env.splice);
                                  FStar_TypeChecker_Env.mpreprocess =
                                    (uu___7.FStar_TypeChecker_Env.mpreprocess);
                                  FStar_TypeChecker_Env.postprocess =
                                    (uu___7.FStar_TypeChecker_Env.postprocess);
                                  FStar_TypeChecker_Env.identifier_info =
                                    (uu___7.FStar_TypeChecker_Env.identifier_info);
                                  FStar_TypeChecker_Env.tc_hooks =
                                    (uu___7.FStar_TypeChecker_Env.tc_hooks);
                                  FStar_TypeChecker_Env.dsenv =
                                    (uu___7.FStar_TypeChecker_Env.dsenv);
                                  FStar_TypeChecker_Env.nbe =
                                    (uu___7.FStar_TypeChecker_Env.nbe);
                                  FStar_TypeChecker_Env.strict_args_tab =
                                    (uu___7.FStar_TypeChecker_Env.strict_args_tab);
                                  FStar_TypeChecker_Env.erasable_types_tab =
                                    (uu___7.FStar_TypeChecker_Env.erasable_types_tab);
                                  FStar_TypeChecker_Env.enable_defer_to_tac =
                                    (uu___7.FStar_TypeChecker_Env.enable_defer_to_tac);
                                  FStar_TypeChecker_Env.unif_allow_ref_guards
                                    =
                                    (uu___7.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                  FStar_TypeChecker_Env.erase_erasable_args =
                                    (uu___7.FStar_TypeChecker_Env.erase_erasable_args);
                                  FStar_TypeChecker_Env.core_check =
                                    (uu___7.FStar_TypeChecker_Env.core_check)
                                } in
                              let uu___7 =
                                FStar_Tactics_Monad.mk_irrelevant_goal
                                  "joined" nenv ng goal_sc (rangeof g1)
                                  g1.FStar_Tactics_Types.opts
                                  g1.FStar_Tactics_Types.label in
                              FStar_Tactics_Monad.op_let_Bang uu___7
                                (fun goal ->
                                   let uu___8 =
                                     FStar_Tactics_Monad.if_verbose
                                       (fun uu___9 ->
                                          let uu___10 =
                                            FStar_Tactics_Printing.goal_to_string_verbose
                                              g1 in
                                          let uu___11 =
                                            FStar_Tactics_Printing.goal_to_string_verbose
                                              g2 in
                                          let uu___12 =
                                            FStar_Tactics_Printing.goal_to_string_verbose
                                              goal in
                                          FStar_Compiler_Util.print3
                                            "join_goals of\n(%s)\nand\n(%s)\n= (%s)\n"
                                            uu___10 uu___11 uu___12) in
                                   FStar_Tactics_Monad.op_let_Bang uu___8
                                     (fun uu___9 ->
                                        FStar_Tactics_Monad.ret goal))))))
let (join : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
      (fun ps ->
         match ps.FStar_Tactics_Types.goals with
         | g1::g2::gs ->
             let uu___1 =
               FStar_Tactics_Monad.set
                 {
                   FStar_Tactics_Types.main_context =
                     (ps.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (ps.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals = gs;
                   FStar_Tactics_Types.smt_goals =
                     (ps.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (ps.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (ps.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (ps.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (ps.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (ps.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state =
                     (ps.FStar_Tactics_Types.local_state);
                   FStar_Tactics_Types.urgency =
                     (ps.FStar_Tactics_Types.urgency)
                 } in
             FStar_Tactics_Monad.op_let_Bang uu___1
               (fun uu___2 ->
                  let uu___3 = join_goals g1 g2 in
                  FStar_Tactics_Monad.op_let_Bang uu___3
                    (fun g12 -> FStar_Tactics_Monad.add_goals [g12]))
         | uu___1 -> FStar_Tactics_Monad.fail "join: less than 2 goals")
let (set_options : Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun s ->
    let uu___ =
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
        (fun g ->
           FStar_Options.push ();
           (let uu___3 =
              FStar_Compiler_Util.smap_copy g.FStar_Tactics_Types.opts in
            FStar_Options.set uu___3);
           (let res = FStar_Options.set_options s in
            let opts' = FStar_Options.peek () in
            FStar_Options.pop ();
            (match res with
             | FStar_Getopt.Success ->
                 let g' =
                   {
                     FStar_Tactics_Types.goal_main_env =
                       (g.FStar_Tactics_Types.goal_main_env);
                     FStar_Tactics_Types.goal_ctx_uvar =
                       (g.FStar_Tactics_Types.goal_ctx_uvar);
                     FStar_Tactics_Types.opts = opts';
                     FStar_Tactics_Types.is_guard =
                       (g.FStar_Tactics_Types.is_guard);
                     FStar_Tactics_Types.label =
                       (g.FStar_Tactics_Types.label)
                   } in
                 FStar_Tactics_Monad.replace_cur g'
             | FStar_Getopt.Error err ->
                 fail2 "Setting options `%s` failed: %s" s err
             | FStar_Getopt.Help ->
                 fail1 "Setting options `%s` failed (got `Help`?)" s))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "set_options") uu___
let (top_env : unit -> env FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.bind FStar_Tactics_Monad.get
      (fun ps ->
         FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
           ps.FStar_Tactics_Types.main_context)
let (lax_on : unit -> Prims.bool FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun g ->
         let uu___1 =
           (FStar_Options.lax ()) ||
             (let uu___2 = FStar_Tactics_Types.goal_env g in
              uu___2.FStar_TypeChecker_Env.lax) in
         FStar_Tactics_Monad.ret uu___1)
let (unquote :
  FStar_Syntax_Syntax.typ ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun tm ->
      let uu___ =
        let uu___1 =
          FStar_Tactics_Monad.if_verbose
            (fun uu___2 ->
               let uu___3 = FStar_Syntax_Print.term_to_string tm in
               FStar_Compiler_Util.print1 "unquote: tm = %s\n" uu___3) in
        FStar_Tactics_Monad.op_let_Bang uu___1
          (fun uu___2 ->
             FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
               (fun goal ->
                  let env1 =
                    let uu___3 = FStar_Tactics_Types.goal_env goal in
                    FStar_TypeChecker_Env.set_expected_typ uu___3 ty in
                  let uu___3 = __tc_ghost env1 tm in
                  FStar_Tactics_Monad.op_let_Bang uu___3
                    (fun uu___4 ->
                       match uu___4 with
                       | (tm1, typ, guard) ->
                           let uu___5 =
                             FStar_Tactics_Monad.if_verbose
                               (fun uu___6 ->
                                  let uu___7 =
                                    FStar_Syntax_Print.term_to_string tm1 in
                                  FStar_Compiler_Util.print1
                                    "unquote: tm' = %s\n" uu___7) in
                           FStar_Tactics_Monad.op_let_Bang uu___5
                             (fun uu___6 ->
                                let uu___7 =
                                  FStar_Tactics_Monad.if_verbose
                                    (fun uu___8 ->
                                       let uu___9 =
                                         FStar_Syntax_Print.term_to_string
                                           typ in
                                       FStar_Compiler_Util.print1
                                         "unquote: typ = %s\n" uu___9) in
                                FStar_Tactics_Monad.op_let_Bang uu___7
                                  (fun uu___8 ->
                                     let uu___9 =
                                       let uu___10 =
                                         let uu___11 =
                                           should_check_goal_uvar goal in
                                         FStar_Pervasives_Native.Some uu___11 in
                                       proc_guard "unquote" env1 guard
                                         uu___10 (rangeof goal) in
                                     FStar_Tactics_Monad.op_let_Bang uu___9
                                       (fun uu___10 ->
                                          FStar_Tactics_Monad.ret tm1)))))) in
      FStar_Compiler_Effect.op_Less_Bar
        (FStar_Tactics_Monad.wrap_err "unquote") uu___
let (uvar_env :
  env ->
    FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
        (fun ps ->
           let uu___ =
             match ty with
             | FStar_Pervasives_Native.Some ty1 ->
                 let env2 =
                   let uu___1 =
                     let uu___2 = FStar_Syntax_Util.type_u () in
                     FStar_Compiler_Effect.op_Bar_Greater uu___2
                       FStar_Pervasives_Native.fst in
                   FStar_TypeChecker_Env.set_expected_typ env1 uu___1 in
                 let uu___1 = __tc_ghost env2 ty1 in
                 FStar_Tactics_Monad.op_let_Bang uu___1
                   (fun uu___2 ->
                      match uu___2 with
                      | (ty2, uu___3, g) ->
                          FStar_Tactics_Monad.ret
                            (ty2, g, (ty2.FStar_Syntax_Syntax.pos)))
             | FStar_Pervasives_Native.None ->
                 let uu___1 =
                   let uu___2 =
                     let uu___3 = FStar_Syntax_Util.type_u () in
                     FStar_Compiler_Effect.op_Less_Bar
                       FStar_Pervasives_Native.fst uu___3 in
                   FStar_Tactics_Monad.new_uvar "uvar_env.2" env1 uu___2
                     FStar_Pervasives_Native.None []
                     ps.FStar_Tactics_Types.entry_range in
                 FStar_Tactics_Monad.op_let_Bang uu___1
                   (fun uu___2 ->
                      match uu___2 with
                      | (typ, uvar_typ) ->
                          FStar_Tactics_Monad.ret
                            (typ, FStar_TypeChecker_Env.trivial_guard,
                              FStar_Compiler_Range_Type.dummyRange)) in
           FStar_Tactics_Monad.op_let_Bang uu___
             (fun uu___1 ->
                match uu___1 with
                | (typ, g, r) ->
                    let uu___2 =
                      proc_guard "uvar_env_typ" env1 g
                        FStar_Pervasives_Native.None r in
                    FStar_Tactics_Monad.op_let_Bang uu___2
                      (fun uu___3 ->
                         let uu___4 =
                           FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ
                             FStar_Pervasives_Native.None []
                             ps.FStar_Tactics_Types.entry_range in
                         FStar_Tactics_Monad.op_let_Bang uu___4
                           (fun uu___5 ->
                              match uu___5 with
                              | (t, uvar_t) -> FStar_Tactics_Monad.ret t))))
let (ghost_uvar_env :
  env ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun env1 ->
    fun ty ->
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
        (fun ps ->
           let uu___ = __tc_ghost env1 ty in
           FStar_Tactics_Monad.op_let_Bang uu___
             (fun uu___1 ->
                match uu___1 with
                | (typ, uu___2, g) ->
                    let uu___3 =
                      proc_guard "ghost_uvar_env_typ" env1 g
                        FStar_Pervasives_Native.None
                        ty.FStar_Syntax_Syntax.pos in
                    FStar_Tactics_Monad.op_let_Bang uu___3
                      (fun uu___4 ->
                         let uu___5 =
                           FStar_Tactics_Monad.new_uvar "uvar_env" env1 typ
                             (FStar_Pervasives_Native.Some
                                (FStar_Syntax_Syntax.Allow_ghost
                                   "User ghost uvar")) []
                             ps.FStar_Tactics_Types.entry_range in
                         FStar_Tactics_Monad.op_let_Bang uu___5
                           (fun uu___6 ->
                              match uu___6 with
                              | (t, uvar_t) -> FStar_Tactics_Monad.ret t))))
let (fresh_universe_uvar :
  unit -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      let uu___2 = FStar_Syntax_Util.type_u () in
      FStar_Compiler_Effect.op_Bar_Greater uu___2 FStar_Pervasives_Native.fst in
    FStar_Compiler_Effect.op_Bar_Greater uu___1 FStar_Tactics_Monad.ret
let (unshelve : FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac) =
  fun t ->
    let uu___ =
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
        (fun ps ->
           let env1 = ps.FStar_Tactics_Types.main_context in
           let opts =
             match ps.FStar_Tactics_Types.goals with
             | g::uu___1 -> g.FStar_Tactics_Types.opts
             | uu___1 -> FStar_Options.peek () in
           let uu___1 = FStar_Syntax_Util.head_and_args t in
           match uu___1 with
           | ({
                FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_uvar
                  (ctx_uvar, uu___2);
                FStar_Syntax_Syntax.pos = uu___3;
                FStar_Syntax_Syntax.vars = uu___4;
                FStar_Syntax_Syntax.hash_code = uu___5;_},
              uu___6) ->
               let env2 =
                 {
                   FStar_TypeChecker_Env.solver =
                     (env1.FStar_TypeChecker_Env.solver);
                   FStar_TypeChecker_Env.range =
                     (env1.FStar_TypeChecker_Env.range);
                   FStar_TypeChecker_Env.curmodule =
                     (env1.FStar_TypeChecker_Env.curmodule);
                   FStar_TypeChecker_Env.gamma =
                     (ctx_uvar.FStar_Syntax_Syntax.ctx_uvar_gamma);
                   FStar_TypeChecker_Env.gamma_sig =
                     (env1.FStar_TypeChecker_Env.gamma_sig);
                   FStar_TypeChecker_Env.gamma_cache =
                     (env1.FStar_TypeChecker_Env.gamma_cache);
                   FStar_TypeChecker_Env.modules =
                     (env1.FStar_TypeChecker_Env.modules);
                   FStar_TypeChecker_Env.expected_typ =
                     (env1.FStar_TypeChecker_Env.expected_typ);
                   FStar_TypeChecker_Env.sigtab =
                     (env1.FStar_TypeChecker_Env.sigtab);
                   FStar_TypeChecker_Env.attrtab =
                     (env1.FStar_TypeChecker_Env.attrtab);
                   FStar_TypeChecker_Env.instantiate_imp =
                     (env1.FStar_TypeChecker_Env.instantiate_imp);
                   FStar_TypeChecker_Env.effects =
                     (env1.FStar_TypeChecker_Env.effects);
                   FStar_TypeChecker_Env.generalize =
                     (env1.FStar_TypeChecker_Env.generalize);
                   FStar_TypeChecker_Env.letrecs =
                     (env1.FStar_TypeChecker_Env.letrecs);
                   FStar_TypeChecker_Env.top_level =
                     (env1.FStar_TypeChecker_Env.top_level);
                   FStar_TypeChecker_Env.check_uvars =
                     (env1.FStar_TypeChecker_Env.check_uvars);
                   FStar_TypeChecker_Env.use_eq_strict =
                     (env1.FStar_TypeChecker_Env.use_eq_strict);
                   FStar_TypeChecker_Env.is_iface =
                     (env1.FStar_TypeChecker_Env.is_iface);
                   FStar_TypeChecker_Env.admit =
                     (env1.FStar_TypeChecker_Env.admit);
                   FStar_TypeChecker_Env.lax =
                     (env1.FStar_TypeChecker_Env.lax);
                   FStar_TypeChecker_Env.lax_universes =
                     (env1.FStar_TypeChecker_Env.lax_universes);
                   FStar_TypeChecker_Env.phase1 =
                     (env1.FStar_TypeChecker_Env.phase1);
                   FStar_TypeChecker_Env.failhard =
                     (env1.FStar_TypeChecker_Env.failhard);
                   FStar_TypeChecker_Env.nosynth =
                     (env1.FStar_TypeChecker_Env.nosynth);
                   FStar_TypeChecker_Env.uvar_subtyping =
                     (env1.FStar_TypeChecker_Env.uvar_subtyping);
                   FStar_TypeChecker_Env.intactics =
                     (env1.FStar_TypeChecker_Env.intactics);
                   FStar_TypeChecker_Env.nocoerce =
                     (env1.FStar_TypeChecker_Env.nocoerce);
                   FStar_TypeChecker_Env.tc_term =
                     (env1.FStar_TypeChecker_Env.tc_term);
                   FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                     (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                   FStar_TypeChecker_Env.universe_of =
                     (env1.FStar_TypeChecker_Env.universe_of);
                   FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                     (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                   FStar_TypeChecker_Env.teq_nosmt_force =
                     (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                   FStar_TypeChecker_Env.subtype_nosmt_force =
                     (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                   FStar_TypeChecker_Env.qtbl_name_and_index =
                     (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                   FStar_TypeChecker_Env.normalized_eff_names =
                     (env1.FStar_TypeChecker_Env.normalized_eff_names);
                   FStar_TypeChecker_Env.fv_delta_depths =
                     (env1.FStar_TypeChecker_Env.fv_delta_depths);
                   FStar_TypeChecker_Env.proof_ns =
                     (env1.FStar_TypeChecker_Env.proof_ns);
                   FStar_TypeChecker_Env.synth_hook =
                     (env1.FStar_TypeChecker_Env.synth_hook);
                   FStar_TypeChecker_Env.try_solve_implicits_hook =
                     (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                   FStar_TypeChecker_Env.splice =
                     (env1.FStar_TypeChecker_Env.splice);
                   FStar_TypeChecker_Env.mpreprocess =
                     (env1.FStar_TypeChecker_Env.mpreprocess);
                   FStar_TypeChecker_Env.postprocess =
                     (env1.FStar_TypeChecker_Env.postprocess);
                   FStar_TypeChecker_Env.identifier_info =
                     (env1.FStar_TypeChecker_Env.identifier_info);
                   FStar_TypeChecker_Env.tc_hooks =
                     (env1.FStar_TypeChecker_Env.tc_hooks);
                   FStar_TypeChecker_Env.dsenv =
                     (env1.FStar_TypeChecker_Env.dsenv);
                   FStar_TypeChecker_Env.nbe =
                     (env1.FStar_TypeChecker_Env.nbe);
                   FStar_TypeChecker_Env.strict_args_tab =
                     (env1.FStar_TypeChecker_Env.strict_args_tab);
                   FStar_TypeChecker_Env.erasable_types_tab =
                     (env1.FStar_TypeChecker_Env.erasable_types_tab);
                   FStar_TypeChecker_Env.enable_defer_to_tac =
                     (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                   FStar_TypeChecker_Env.unif_allow_ref_guards =
                     (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                   FStar_TypeChecker_Env.erase_erasable_args =
                     (env1.FStar_TypeChecker_Env.erase_erasable_args);
                   FStar_TypeChecker_Env.core_check =
                     (env1.FStar_TypeChecker_Env.core_check)
                 } in
               let g =
                 FStar_Tactics_Types.mk_goal env2 ctx_uvar opts false "" in
               let g1 = bnorm_goal g in FStar_Tactics_Monad.add_goals [g1]
           | uu___2 -> FStar_Tactics_Monad.fail "not a uvar") in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "unshelve") uu___
let (tac_and :
  Prims.bool FStar_Tactics_Monad.tac ->
    Prims.bool FStar_Tactics_Monad.tac -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      let comp =
        FStar_Tactics_Monad.op_let_Bang t1
          (fun uu___ ->
             if uu___
             then
               FStar_Tactics_Monad.op_let_Bang t2
                 (fun uu___1 ->
                    if uu___1
                    then FStar_Tactics_Monad.ret true
                    else FStar_Tactics_Monad.fail "")
             else FStar_Tactics_Monad.fail "") in
      let uu___ = FStar_Tactics_Monad.trytac comp in
      FStar_Tactics_Monad.op_let_Bang uu___
        (fun uu___1 ->
           match uu___1 with
           | FStar_Pervasives_Native.Some (true) ->
               FStar_Tactics_Monad.ret true
           | FStar_Pervasives_Native.Some (false) -> failwith "impossible"
           | FStar_Pervasives_Native.None -> FStar_Tactics_Monad.ret false)
let (match_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
            (fun ps ->
               let uu___1 = __tc e t1 in
               FStar_Tactics_Monad.op_let_Bang uu___1
                 (fun uu___2 ->
                    match uu___2 with
                    | (t11, ty1, g1) ->
                        let uu___3 = __tc e t2 in
                        FStar_Tactics_Monad.op_let_Bang uu___3
                          (fun uu___4 ->
                             match uu___4 with
                             | (t21, ty2, g2) ->
                                 let uu___5 =
                                   proc_guard "match_env g1" e g1
                                     FStar_Pervasives_Native.None
                                     ps.FStar_Tactics_Types.entry_range in
                                 FStar_Tactics_Monad.op_let_Bang uu___5
                                   (fun uu___6 ->
                                      let uu___7 =
                                        proc_guard "match_env g2" e g2
                                          FStar_Pervasives_Native.None
                                          ps.FStar_Tactics_Types.entry_range in
                                      FStar_Tactics_Monad.op_let_Bang uu___7
                                        (fun uu___8 ->
                                           let must_tot = true in
                                           let uu___9 =
                                             do_match must_tot e ty1 ty2 in
                                           let uu___10 =
                                             do_match must_tot e t11 t21 in
                                           tac_and uu___9 uu___10))))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "match_env") uu___
let (unify_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
            (fun ps ->
               let uu___1 = __tc e t1 in
               FStar_Tactics_Monad.op_let_Bang uu___1
                 (fun uu___2 ->
                    match uu___2 with
                    | (t11, ty1, g1) ->
                        let uu___3 = __tc e t2 in
                        FStar_Tactics_Monad.op_let_Bang uu___3
                          (fun uu___4 ->
                             match uu___4 with
                             | (t21, ty2, g2) ->
                                 let uu___5 =
                                   proc_guard "unify_env g1" e g1
                                     FStar_Pervasives_Native.None
                                     ps.FStar_Tactics_Types.entry_range in
                                 FStar_Tactics_Monad.op_let_Bang uu___5
                                   (fun uu___6 ->
                                      let uu___7 =
                                        proc_guard "unify_env g2" e g2
                                          FStar_Pervasives_Native.None
                                          ps.FStar_Tactics_Types.entry_range in
                                      FStar_Tactics_Monad.op_let_Bang uu___7
                                        (fun uu___8 ->
                                           let must_tot = true in
                                           let uu___9 =
                                             do_unify must_tot e ty1 ty2 in
                                           let uu___10 =
                                             do_unify must_tot e t11 t21 in
                                           tac_and uu___9 uu___10))))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "unify_env") uu___
let (unify_guard_env :
  env ->
    FStar_Syntax_Syntax.term ->
      FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun t1 ->
      fun t2 ->
        let uu___ =
          FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
            (fun ps ->
               let uu___1 = __tc e t1 in
               FStar_Tactics_Monad.op_let_Bang uu___1
                 (fun uu___2 ->
                    match uu___2 with
                    | (t11, ty1, g1) ->
                        let uu___3 = __tc e t2 in
                        FStar_Tactics_Monad.op_let_Bang uu___3
                          (fun uu___4 ->
                             match uu___4 with
                             | (t21, ty2, g2) ->
                                 let uu___5 =
                                   proc_guard "unify_guard_env g1" e g1
                                     FStar_Pervasives_Native.None
                                     ps.FStar_Tactics_Types.entry_range in
                                 FStar_Tactics_Monad.op_let_Bang uu___5
                                   (fun uu___6 ->
                                      let uu___7 =
                                        proc_guard "unify_guard_env g2" e g2
                                          FStar_Pervasives_Native.None
                                          ps.FStar_Tactics_Types.entry_range in
                                      FStar_Tactics_Monad.op_let_Bang uu___7
                                        (fun uu___8 ->
                                           let must_tot = true in
                                           let uu___9 =
                                             do_unify_maybe_guards true
                                               must_tot e ty1 ty2 in
                                           FStar_Tactics_Monad.op_let_Bang
                                             uu___9
                                             (fun uu___10 ->
                                                match uu___10 with
                                                | FStar_Pervasives_Native.None
                                                    ->
                                                    FStar_Tactics_Monad.ret
                                                      false
                                                | FStar_Pervasives_Native.Some
                                                    g11 ->
                                                    let uu___11 =
                                                      do_unify_maybe_guards
                                                        true must_tot e t11
                                                        t21 in
                                                    FStar_Tactics_Monad.op_let_Bang
                                                      uu___11
                                                      (fun uu___12 ->
                                                         match uu___12 with
                                                         | FStar_Pervasives_Native.None
                                                             ->
                                                             FStar_Tactics_Monad.ret
                                                               false
                                                         | FStar_Pervasives_Native.Some
                                                             g21 ->
                                                             let formula =
                                                               let uu___13 =
                                                                 guard_formula
                                                                   g11 in
                                                               let uu___14 =
                                                                 guard_formula
                                                                   g21 in
                                                               FStar_Syntax_Util.mk_conj
                                                                 uu___13
                                                                 uu___14 in
                                                             let uu___13 =
                                                               FStar_Tactics_Monad.goal_of_guard
                                                                 "unify_guard_env.g2"
                                                                 e formula
                                                                 FStar_Pervasives_Native.None
                                                                 ps.FStar_Tactics_Types.entry_range in
                                                             FStar_Tactics_Monad.op_let_Bang
                                                               uu___13
                                                               (fun goal ->
                                                                  let uu___14
                                                                    =
                                                                    FStar_Tactics_Monad.push_goals
                                                                    [goal] in
                                                                  FStar_Tactics_Monad.op_let_Bang
                                                                    uu___14
                                                                    (
                                                                    fun
                                                                    uu___15
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    true))))))))) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "unify_guard_env") uu___
let (launch_process :
  Prims.string ->
    Prims.string Prims.list ->
      Prims.string -> Prims.string FStar_Tactics_Monad.tac)
  =
  fun prog ->
    fun args ->
      fun input ->
        FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.idtac
          (fun uu___ ->
             let uu___1 = FStar_Options.unsafe_tactic_exec () in
             if uu___1
             then
               let s =
                 FStar_Compiler_Util.run_process "tactic_launch" prog args
                   (FStar_Pervasives_Native.Some input) in
               FStar_Tactics_Monad.ret s
             else
               FStar_Tactics_Monad.fail
                 "launch_process: will not run anything unless --unsafe_tactic_exec is provided")
let (fresh_bv_named :
  Prims.string -> FStar_Syntax_Syntax.bv FStar_Tactics_Monad.tac) =
  fun nm ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.idtac
      (fun uu___ ->
         let uu___1 =
           FStar_Syntax_Syntax.gen_bv nm FStar_Pervasives_Native.None
             FStar_Syntax_Syntax.tun in
         FStar_Tactics_Monad.ret uu___1)
let (change : FStar_Syntax_Syntax.typ -> unit FStar_Tactics_Monad.tac) =
  fun ty ->
    let uu___ =
      let uu___1 =
        FStar_Tactics_Monad.if_verbose
          (fun uu___2 ->
             let uu___3 = FStar_Syntax_Print.term_to_string ty in
             FStar_Compiler_Util.print1 "change: ty = %s\n" uu___3) in
      FStar_Tactics_Monad.op_let_Bang uu___1
        (fun uu___2 ->
           FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
             (fun g ->
                let uu___3 =
                  let uu___4 = FStar_Tactics_Types.goal_env g in
                  __tc uu___4 ty in
                FStar_Tactics_Monad.op_let_Bang uu___3
                  (fun uu___4 ->
                     match uu___4 with
                     | (ty1, uu___5, guard) ->
                         let uu___6 =
                           let uu___7 = FStar_Tactics_Types.goal_env g in
                           let uu___8 =
                             let uu___9 = should_check_goal_uvar g in
                             FStar_Pervasives_Native.Some uu___9 in
                           proc_guard "change" uu___7 guard uu___8
                             (rangeof g) in
                         FStar_Tactics_Monad.op_let_Bang uu___6
                           (fun uu___7 ->
                              let must_tot = true in
                              let uu___8 =
                                let uu___9 = FStar_Tactics_Types.goal_env g in
                                let uu___10 = FStar_Tactics_Types.goal_type g in
                                do_unify must_tot uu___9 uu___10 ty1 in
                              FStar_Tactics_Monad.op_let_Bang uu___8
                                (fun bb ->
                                   if bb
                                   then
                                     let uu___9 = goal_with_type g ty1 in
                                     FStar_Tactics_Monad.replace_cur uu___9
                                   else
                                     (let steps =
                                        [FStar_TypeChecker_Env.AllowUnboundUniverses;
                                        FStar_TypeChecker_Env.UnfoldUntil
                                          FStar_Syntax_Syntax.delta_constant;
                                        FStar_TypeChecker_Env.Primops] in
                                      let ng =
                                        let uu___10 =
                                          FStar_Tactics_Types.goal_env g in
                                        let uu___11 =
                                          FStar_Tactics_Types.goal_type g in
                                        normalize steps uu___10 uu___11 in
                                      let nty =
                                        let uu___10 =
                                          FStar_Tactics_Types.goal_env g in
                                        normalize steps uu___10 ty1 in
                                      let uu___10 =
                                        let uu___11 =
                                          FStar_Tactics_Types.goal_env g in
                                        do_unify must_tot uu___11 ng nty in
                                      FStar_Tactics_Monad.op_let_Bang uu___10
                                        (fun b ->
                                           if b
                                           then
                                             let uu___11 =
                                               goal_with_type g ty1 in
                                             FStar_Tactics_Monad.replace_cur
                                               uu___11
                                           else
                                             FStar_Tactics_Monad.fail
                                               "not convertible"))))))) in
    FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "change")
      uu___
let (failwhen : Prims.bool -> Prims.string -> unit FStar_Tactics_Monad.tac) =
  fun b ->
    fun msg ->
      if b then FStar_Tactics_Monad.fail msg else FStar_Tactics_Monad.ret ()
let (t_destruct :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.fv * FStar_BigInt.t) Prims.list
      FStar_Tactics_Monad.tac)
  =
  fun s_tm ->
    let uu___ =
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu___1 =
             let uu___2 = FStar_Tactics_Types.goal_env g in __tc uu___2 s_tm in
           FStar_Tactics_Monad.op_let_Bang uu___1
             (fun uu___2 ->
                match uu___2 with
                | (s_tm1, s_ty, guard) ->
                    let uu___3 =
                      let uu___4 = FStar_Tactics_Types.goal_env g in
                      let uu___5 =
                        let uu___6 = should_check_goal_uvar g in
                        FStar_Pervasives_Native.Some uu___6 in
                      proc_guard "destruct" uu___4 guard uu___5 (rangeof g) in
                    FStar_Tactics_Monad.op_let_Bang uu___3
                      (fun uu___4 ->
                         let s_ty1 =
                           let uu___5 = FStar_Tactics_Types.goal_env g in
                           FStar_TypeChecker_Normalize.normalize
                             [FStar_TypeChecker_Env.UnfoldTac;
                             FStar_TypeChecker_Env.Weak;
                             FStar_TypeChecker_Env.HNF;
                             FStar_TypeChecker_Env.UnfoldUntil
                               FStar_Syntax_Syntax.delta_constant] uu___5
                             s_ty in
                         let uu___5 =
                           let uu___6 = FStar_Syntax_Util.unrefine s_ty1 in
                           FStar_Syntax_Util.head_and_args_full uu___6 in
                         match uu___5 with
                         | (h, args) ->
                             let uu___6 =
                               let uu___7 =
                                 let uu___8 = FStar_Syntax_Subst.compress h in
                                 uu___8.FStar_Syntax_Syntax.n in
                               match uu___7 with
                               | FStar_Syntax_Syntax.Tm_fvar fv ->
                                   FStar_Tactics_Monad.ret (fv, [])
                               | FStar_Syntax_Syntax.Tm_uinst (h', us) ->
                                   let uu___8 =
                                     let uu___9 =
                                       FStar_Syntax_Subst.compress h' in
                                     uu___9.FStar_Syntax_Syntax.n in
                                   (match uu___8 with
                                    | FStar_Syntax_Syntax.Tm_fvar fv ->
                                        FStar_Tactics_Monad.ret (fv, us)
                                    | uu___9 ->
                                        failwith
                                          "impossible: uinst over something that's not an fvar")
                               | uu___8 ->
                                   FStar_Tactics_Monad.fail
                                     "type is not an fv" in
                             FStar_Tactics_Monad.op_let_Bang uu___6
                               (fun uu___7 ->
                                  match uu___7 with
                                  | (fv, a_us) ->
                                      let t_lid =
                                        FStar_Syntax_Syntax.lid_of_fv fv in
                                      let uu___8 =
                                        let uu___9 =
                                          FStar_Tactics_Types.goal_env g in
                                        FStar_TypeChecker_Env.lookup_sigelt
                                          uu___9 t_lid in
                                      (match uu___8 with
                                       | FStar_Pervasives_Native.None ->
                                           FStar_Tactics_Monad.fail
                                             "type not found in environment"
                                       | FStar_Pervasives_Native.Some se ->
                                           (match se.FStar_Syntax_Syntax.sigel
                                            with
                                            | FStar_Syntax_Syntax.Sig_inductive_typ
                                                {
                                                  FStar_Syntax_Syntax.lid =
                                                    uu___9;
                                                  FStar_Syntax_Syntax.us =
                                                    t_us;
                                                  FStar_Syntax_Syntax.params
                                                    = t_ps;
                                                  FStar_Syntax_Syntax.num_uniform_params
                                                    = uu___10;
                                                  FStar_Syntax_Syntax.t =
                                                    t_ty;
                                                  FStar_Syntax_Syntax.mutuals
                                                    = mut;
                                                  FStar_Syntax_Syntax.ds =
                                                    c_lids;_}
                                                ->
                                                let erasable =
                                                  FStar_Syntax_Util.has_attribute
                                                    se.FStar_Syntax_Syntax.sigattrs
                                                    FStar_Parser_Const.erasable_attr in
                                                let uu___11 =
                                                  let uu___12 =
                                                    erasable &&
                                                      (let uu___13 =
                                                         FStar_Tactics_Types.is_irrelevant
                                                           g in
                                                       Prims.op_Negation
                                                         uu___13) in
                                                  failwhen uu___12
                                                    "cannot destruct erasable type to solve proof-relevant goal" in
                                                FStar_Tactics_Monad.op_let_Bang
                                                  uu___11
                                                  (fun uu___12 ->
                                                     let uu___13 =
                                                       failwhen
                                                         ((FStar_Compiler_List.length
                                                             a_us)
                                                            <>
                                                            (FStar_Compiler_List.length
                                                               t_us))
                                                         "t_us don't match?" in
                                                     FStar_Tactics_Monad.op_let_Bang
                                                       uu___13
                                                       (fun uu___14 ->
                                                          let uu___15 =
                                                            FStar_Syntax_Subst.open_term
                                                              t_ps t_ty in
                                                          match uu___15 with
                                                          | (t_ps1, t_ty1) ->
                                                              let uu___16 =
                                                                FStar_Tactics_Monad.mapM
                                                                  (fun c_lid
                                                                    ->
                                                                    let uu___17
                                                                    =
                                                                    let uu___18
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    FStar_TypeChecker_Env.lookup_sigelt
                                                                    uu___18
                                                                    c_lid in
                                                                    match uu___17
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.None
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "ctor not found?"
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    se1 ->
                                                                    (match 
                                                                    se1.FStar_Syntax_Syntax.sigel
                                                                    with
                                                                    | 
                                                                    FStar_Syntax_Syntax.Sig_datacon
                                                                    {
                                                                    FStar_Syntax_Syntax.lid1
                                                                    = uu___18;
                                                                    FStar_Syntax_Syntax.us1
                                                                    = c_us;
                                                                    FStar_Syntax_Syntax.t1
                                                                    = c_ty;
                                                                    FStar_Syntax_Syntax.ty_lid
                                                                    = uu___19;
                                                                    FStar_Syntax_Syntax.num_ty_params
                                                                    = nparam;
                                                                    FStar_Syntax_Syntax.mutuals1
                                                                    = mut1;_}
                                                                    ->
                                                                    let fv1 =
                                                                    FStar_Syntax_Syntax.lid_as_fv
                                                                    c_lid
                                                                    (FStar_Pervasives_Native.Some
                                                                    FStar_Syntax_Syntax.Data_ctor) in
                                                                    let uu___20
                                                                    =
                                                                    failwhen
                                                                    ((FStar_Compiler_List.length
                                                                    a_us) <>
                                                                    (FStar_Compiler_List.length
                                                                    c_us))
                                                                    "t_us don't match?" in
                                                                    FStar_Tactics_Monad.op_let_Bang
                                                                    uu___20
                                                                    (fun
                                                                    uu___21
                                                                    ->
                                                                    let s =
                                                                    FStar_TypeChecker_Env.mk_univ_subst
                                                                    c_us a_us in
                                                                    let c_ty1
                                                                    =
                                                                    FStar_Syntax_Subst.subst
                                                                    s c_ty in
                                                                    let uu___22
                                                                    =
                                                                    FStar_TypeChecker_Env.inst_tscheme
                                                                    (c_us,
                                                                    c_ty1) in
                                                                    match uu___22
                                                                    with
                                                                    | 
                                                                    (c_us1,
                                                                    c_ty2) ->
                                                                    let uu___23
                                                                    =
                                                                    FStar_Syntax_Util.arrow_formals_comp
                                                                    c_ty2 in
                                                                    (match uu___23
                                                                    with
                                                                    | 
                                                                    (bs,
                                                                    comp) ->
                                                                    let uu___24
                                                                    =
                                                                    let rename_bv
                                                                    bv =
                                                                    let ppname
                                                                    =
                                                                    bv.FStar_Syntax_Syntax.ppname in
                                                                    let ppname1
                                                                    =
                                                                    let uu___25
                                                                    =
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    FStar_Ident.string_of_id
                                                                    ppname in
                                                                    Prims.op_Hat
                                                                    "a"
                                                                    uu___27 in
                                                                    let uu___27
                                                                    =
                                                                    FStar_Ident.range_of_id
                                                                    ppname in
                                                                    (uu___26,
                                                                    uu___27) in
                                                                    FStar_Ident.mk_ident
                                                                    uu___25 in
                                                                    FStar_Syntax_Syntax.freshen_bv
                                                                    {
                                                                    FStar_Syntax_Syntax.ppname
                                                                    = ppname1;
                                                                    FStar_Syntax_Syntax.index
                                                                    =
                                                                    (bv.FStar_Syntax_Syntax.index);
                                                                    FStar_Syntax_Syntax.sort
                                                                    =
                                                                    (bv.FStar_Syntax_Syntax.sort)
                                                                    } in
                                                                    let bs' =
                                                                    FStar_Compiler_List.map
                                                                    (fun b ->
                                                                    let uu___25
                                                                    =
                                                                    rename_bv
                                                                    b.FStar_Syntax_Syntax.binder_bv in
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = uu___25;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_qual);
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_positivity);
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    =
                                                                    (b.FStar_Syntax_Syntax.binder_attrs)
                                                                    }) bs in
                                                                    let subst
                                                                    =
                                                                    FStar_Compiler_List.map2
                                                                    (fun
                                                                    uu___25
                                                                    ->
                                                                    fun
                                                                    uu___26
                                                                    ->
                                                                    match 
                                                                    (uu___25,
                                                                    uu___26)
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___27;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___28;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___29;_},
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv';
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___30;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___31;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___32;_})
                                                                    ->
                                                                    let uu___33
                                                                    =
                                                                    let uu___34
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    bv' in
                                                                    (bv,
                                                                    uu___34) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu___33)
                                                                    bs bs' in
                                                                    let uu___25
                                                                    =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs' in
                                                                    let uu___26
                                                                    =
                                                                    FStar_Syntax_Subst.subst_comp
                                                                    subst
                                                                    comp in
                                                                    (uu___25,
                                                                    uu___26) in
                                                                    (match uu___24
                                                                    with
                                                                    | 
                                                                    (bs1,
                                                                    comp1) ->
                                                                    let uu___25
                                                                    =
                                                                    FStar_Compiler_List.splitAt
                                                                    nparam
                                                                    bs1 in
                                                                    (match uu___25
                                                                    with
                                                                    | 
                                                                    (d_ps,
                                                                    bs2) ->
                                                                    let uu___26
                                                                    =
                                                                    let uu___27
                                                                    =
                                                                    let uu___28
                                                                    =
                                                                    FStar_Syntax_Util.is_total_comp
                                                                    comp1 in
                                                                    Prims.op_Negation
                                                                    uu___28 in
                                                                    failwhen
                                                                    uu___27
                                                                    "not total?" in
                                                                    FStar_Tactics_Monad.op_let_Bang
                                                                    uu___26
                                                                    (fun
                                                                    uu___27
                                                                    ->
                                                                    let mk_pat
                                                                    p =
                                                                    {
                                                                    FStar_Syntax_Syntax.v
                                                                    = p;
                                                                    FStar_Syntax_Syntax.p
                                                                    =
                                                                    (s_tm1.FStar_Syntax_Syntax.pos)
                                                                    } in
                                                                    let is_imp
                                                                    uu___28 =
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    FStar_Pervasives_Native.Some
                                                                    (FStar_Syntax_Syntax.Implicit
                                                                    uu___29)
                                                                    -> true
                                                                    | 
                                                                    uu___29
                                                                    -> false in
                                                                    let uu___28
                                                                    =
                                                                    FStar_Compiler_List.splitAt
                                                                    nparam
                                                                    args in
                                                                    match uu___28
                                                                    with
                                                                    | 
                                                                    (a_ps,
                                                                    a_is) ->
                                                                    let uu___29
                                                                    =
                                                                    failwhen
                                                                    ((FStar_Compiler_List.length
                                                                    a_ps) <>
                                                                    (FStar_Compiler_List.length
                                                                    d_ps))
                                                                    "params not match?" in
                                                                    FStar_Tactics_Monad.op_let_Bang
                                                                    uu___29
                                                                    (fun
                                                                    uu___30
                                                                    ->
                                                                    let d_ps_a_ps
                                                                    =
                                                                    FStar_Compiler_List.zip
                                                                    d_ps a_ps in
                                                                    let subst
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___32;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___33;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___34;_},
                                                                    (t,
                                                                    uu___35))
                                                                    ->
                                                                    FStar_Syntax_Syntax.NT
                                                                    (bv, t))
                                                                    d_ps_a_ps in
                                                                    let bs3 =
                                                                    FStar_Syntax_Subst.subst_binders
                                                                    subst bs2 in
                                                                    let subpats_1
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    ({
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = uu___32;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___33;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___34;_},
                                                                    (t,
                                                                    uu___35))
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_dot_term
                                                                    (FStar_Pervasives_Native.Some
                                                                    t))),
                                                                    true))
                                                                    d_ps_a_ps in
                                                                    let subpats_2
                                                                    =
                                                                    FStar_Compiler_List.map
                                                                    (fun
                                                                    uu___31
                                                                    ->
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    {
                                                                    FStar_Syntax_Syntax.binder_bv
                                                                    = bv;
                                                                    FStar_Syntax_Syntax.binder_qual
                                                                    = bq;
                                                                    FStar_Syntax_Syntax.binder_positivity
                                                                    = uu___32;
                                                                    FStar_Syntax_Syntax.binder_attrs
                                                                    = uu___33;_}
                                                                    ->
                                                                    ((mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_var
                                                                    bv)),
                                                                    (is_imp
                                                                    bq))) bs3 in
                                                                    let subpats
                                                                    =
                                                                    FStar_Compiler_List.op_At
                                                                    subpats_1
                                                                    subpats_2 in
                                                                    let pat =
                                                                    mk_pat
                                                                    (FStar_Syntax_Syntax.Pat_cons
                                                                    (fv1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    a_us),
                                                                    subpats)) in
                                                                    let env1
                                                                    =
                                                                    FStar_Tactics_Types.goal_env
                                                                    g in
                                                                    let cod =
                                                                    FStar_Tactics_Types.goal_type
                                                                    g in
                                                                    let equ =
                                                                    env1.FStar_TypeChecker_Env.universe_of
                                                                    env1
                                                                    s_ty1 in
                                                                    let uu___31
                                                                    =
                                                                    FStar_TypeChecker_TcTerm.tc_pat
                                                                    {
                                                                    FStar_TypeChecker_Env.solver
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.solver);
                                                                    FStar_TypeChecker_Env.range
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.range);
                                                                    FStar_TypeChecker_Env.curmodule
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.curmodule);
                                                                    FStar_TypeChecker_Env.gamma
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.gamma);
                                                                    FStar_TypeChecker_Env.gamma_sig
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.gamma_sig);
                                                                    FStar_TypeChecker_Env.gamma_cache
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.gamma_cache);
                                                                    FStar_TypeChecker_Env.modules
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.modules);
                                                                    FStar_TypeChecker_Env.expected_typ
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.expected_typ);
                                                                    FStar_TypeChecker_Env.sigtab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.sigtab);
                                                                    FStar_TypeChecker_Env.attrtab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.attrtab);
                                                                    FStar_TypeChecker_Env.instantiate_imp
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.instantiate_imp);
                                                                    FStar_TypeChecker_Env.effects
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.effects);
                                                                    FStar_TypeChecker_Env.generalize
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.generalize);
                                                                    FStar_TypeChecker_Env.letrecs
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.letrecs);
                                                                    FStar_TypeChecker_Env.top_level
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.top_level);
                                                                    FStar_TypeChecker_Env.check_uvars
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.check_uvars);
                                                                    FStar_TypeChecker_Env.use_eq_strict
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.use_eq_strict);
                                                                    FStar_TypeChecker_Env.is_iface
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.is_iface);
                                                                    FStar_TypeChecker_Env.admit
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.admit);
                                                                    FStar_TypeChecker_Env.lax
                                                                    = true;
                                                                    FStar_TypeChecker_Env.lax_universes
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.lax_universes);
                                                                    FStar_TypeChecker_Env.phase1
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.phase1);
                                                                    FStar_TypeChecker_Env.failhard
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.failhard);
                                                                    FStar_TypeChecker_Env.nosynth
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.nosynth);
                                                                    FStar_TypeChecker_Env.uvar_subtyping
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.uvar_subtyping);
                                                                    FStar_TypeChecker_Env.intactics
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.intactics);
                                                                    FStar_TypeChecker_Env.nocoerce
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.nocoerce);
                                                                    FStar_TypeChecker_Env.tc_term
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.tc_term);
                                                                    FStar_TypeChecker_Env.typeof_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
                                                                    FStar_TypeChecker_Env.universe_of
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.universe_of);
                                                                    FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
                                                                    FStar_TypeChecker_Env.teq_nosmt_force
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.teq_nosmt_force);
                                                                    FStar_TypeChecker_Env.subtype_nosmt_force
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.subtype_nosmt_force);
                                                                    FStar_TypeChecker_Env.qtbl_name_and_index
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.qtbl_name_and_index);
                                                                    FStar_TypeChecker_Env.normalized_eff_names
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.normalized_eff_names);
                                                                    FStar_TypeChecker_Env.fv_delta_depths
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.fv_delta_depths);
                                                                    FStar_TypeChecker_Env.proof_ns
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.proof_ns);
                                                                    FStar_TypeChecker_Env.synth_hook
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.synth_hook);
                                                                    FStar_TypeChecker_Env.try_solve_implicits_hook
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.try_solve_implicits_hook);
                                                                    FStar_TypeChecker_Env.splice
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.splice);
                                                                    FStar_TypeChecker_Env.mpreprocess
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.mpreprocess);
                                                                    FStar_TypeChecker_Env.postprocess
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.postprocess);
                                                                    FStar_TypeChecker_Env.identifier_info
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.identifier_info);
                                                                    FStar_TypeChecker_Env.tc_hooks
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.tc_hooks);
                                                                    FStar_TypeChecker_Env.dsenv
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.dsenv);
                                                                    FStar_TypeChecker_Env.nbe
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.nbe);
                                                                    FStar_TypeChecker_Env.strict_args_tab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.strict_args_tab);
                                                                    FStar_TypeChecker_Env.erasable_types_tab
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.erasable_types_tab);
                                                                    FStar_TypeChecker_Env.enable_defer_to_tac
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.enable_defer_to_tac);
                                                                    FStar_TypeChecker_Env.unif_allow_ref_guards
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.unif_allow_ref_guards);
                                                                    FStar_TypeChecker_Env.erase_erasable_args
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.erase_erasable_args);
                                                                    FStar_TypeChecker_Env.core_check
                                                                    =
                                                                    (env1.FStar_TypeChecker_Env.core_check)
                                                                    } s_ty1
                                                                    pat in
                                                                    match uu___31
                                                                    with
                                                                    | 
                                                                    (uu___32,
                                                                    uu___33,
                                                                    uu___34,
                                                                    uu___35,
                                                                    pat_t,
                                                                    uu___36,
                                                                    _guard_pat,
                                                                    _erasable)
                                                                    ->
                                                                    let eq_b
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStar_Syntax_Util.mk_eq2
                                                                    equ s_ty1
                                                                    s_tm1
                                                                    pat_t in
                                                                    FStar_Syntax_Util.mk_squash
                                                                    FStar_Syntax_Syntax.U_zero
                                                                    uu___38 in
                                                                    FStar_Syntax_Syntax.gen_bv
                                                                    "breq"
                                                                    FStar_Pervasives_Native.None
                                                                    uu___37 in
                                                                    let cod1
                                                                    =
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_binder
                                                                    eq_b in
                                                                    [uu___38] in
                                                                    let uu___38
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod in
                                                                    FStar_Syntax_Util.arrow
                                                                    uu___37
                                                                    uu___38 in
                                                                    let nty =
                                                                    let uu___37
                                                                    =
                                                                    FStar_Syntax_Syntax.mk_Total
                                                                    cod1 in
                                                                    FStar_Syntax_Util.arrow
                                                                    bs3
                                                                    uu___37 in
                                                                    let uu___37
                                                                    =
                                                                    let uu___38
                                                                    =
                                                                    goal_typedness_deps
                                                                    g in
                                                                    FStar_Tactics_Monad.new_uvar
                                                                    "destruct branch"
                                                                    env1 nty
                                                                    FStar_Pervasives_Native.None
                                                                    uu___38
                                                                    (rangeof
                                                                    g) in
                                                                    FStar_Tactics_Monad.op_let_Bang
                                                                    uu___37
                                                                    (fun
                                                                    uu___38
                                                                    ->
                                                                    match uu___38
                                                                    with
                                                                    | 
                                                                    (uvt, uv)
                                                                    ->
                                                                    let g' =
                                                                    FStar_Tactics_Types.mk_goal
                                                                    env1 uv
                                                                    g.FStar_Tactics_Types.opts
                                                                    false
                                                                    g.FStar_Tactics_Types.label in
                                                                    let brt =
                                                                    FStar_Syntax_Util.mk_app_binders
                                                                    uvt bs3 in
                                                                    let brt1
                                                                    =
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    FStar_Syntax_Syntax.as_arg
                                                                    FStar_Syntax_Util.exp_unit in
                                                                    [uu___40] in
                                                                    FStar_Syntax_Util.mk_app
                                                                    brt
                                                                    uu___39 in
                                                                    let br =
                                                                    FStar_Syntax_Subst.close_branch
                                                                    (pat,
                                                                    FStar_Pervasives_Native.None,
                                                                    brt1) in
                                                                    let uu___39
                                                                    =
                                                                    let uu___40
                                                                    =
                                                                    let uu___41
                                                                    =
                                                                    FStar_BigInt.of_int_fs
                                                                    (FStar_Compiler_List.length
                                                                    bs3) in
                                                                    (fv1,
                                                                    uu___41) in
                                                                    (g', br,
                                                                    uu___40) in
                                                                    FStar_Tactics_Monad.ret
                                                                    uu___39)))))))
                                                                    | 
                                                                    uu___18
                                                                    ->
                                                                    FStar_Tactics_Monad.fail
                                                                    "impossible: not a ctor"))
                                                                  c_lids in
                                                              FStar_Tactics_Monad.op_let_Bang
                                                                uu___16
                                                                (fun goal_brs
                                                                   ->
                                                                   let uu___17
                                                                    =
                                                                    FStar_Compiler_List.unzip3
                                                                    goal_brs in
                                                                   match uu___17
                                                                   with
                                                                   | 
                                                                   (goals,
                                                                    brs,
                                                                    infos) ->
                                                                    let w =
                                                                    FStar_Syntax_Syntax.mk
                                                                    (FStar_Syntax_Syntax.Tm_match
                                                                    {
                                                                    FStar_Syntax_Syntax.scrutinee
                                                                    = s_tm1;
                                                                    FStar_Syntax_Syntax.ret_opt
                                                                    =
                                                                    FStar_Pervasives_Native.None;
                                                                    FStar_Syntax_Syntax.brs
                                                                    = brs;
                                                                    FStar_Syntax_Syntax.rc_opt1
                                                                    =
                                                                    FStar_Pervasives_Native.None
                                                                    })
                                                                    s_tm1.FStar_Syntax_Syntax.pos in
                                                                    let uu___18
                                                                    =
                                                                    solve' g
                                                                    w in
                                                                    FStar_Tactics_Monad.op_let_Bang
                                                                    uu___18
                                                                    (fun
                                                                    uu___19
                                                                    ->
                                                                    mark_goal_implicit_already_checked
                                                                    g;
                                                                    (
                                                                    let uu___21
                                                                    =
                                                                    FStar_Tactics_Monad.add_goals
                                                                    goals in
                                                                    FStar_Tactics_Monad.op_let_Bang
                                                                    uu___21
                                                                    (fun
                                                                    uu___22
                                                                    ->
                                                                    FStar_Tactics_Monad.ret
                                                                    infos))))))
                                            | uu___9 ->
                                                FStar_Tactics_Monad.fail
                                                  "not an inductive type")))))) in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "destruct") uu___
let (gather_explicit_guards_for_resolved_goals :
  unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ -> FStar_Tactics_Monad.ret ()
let rec last : 'a . 'a Prims.list -> 'a =
  fun l ->
    match l with
    | [] -> failwith "last: empty list"
    | x::[] -> x
    | uu___::xs -> last xs
let rec init : 'a . 'a Prims.list -> 'a Prims.list =
  fun l ->
    match l with
    | [] -> failwith "init: empty list"
    | x::[] -> []
    | x::xs -> let uu___ = init xs in x :: uu___
let rec (inspect :
  FStar_Syntax_Syntax.term ->
    FStar_Reflection_V1_Data.term_view FStar_Tactics_Monad.tac)
  =
  fun t ->
    let uu___ =
      let uu___1 = top_env () in
      FStar_Tactics_Monad.op_let_Bang uu___1
        (fun e ->
           let t1 = FStar_Syntax_Util.unlazy_emb t in
           let t2 = FStar_Syntax_Subst.compress t1 in
           match t2.FStar_Syntax_Syntax.n with
           | FStar_Syntax_Syntax.Tm_meta
               { FStar_Syntax_Syntax.tm2 = t3;
                 FStar_Syntax_Syntax.meta = uu___2;_}
               -> inspect t3
           | FStar_Syntax_Syntax.Tm_name bv ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_V1_Data.Tv_Var bv)
           | FStar_Syntax_Syntax.Tm_bvar bv ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_V1_Data.Tv_BVar bv)
           | FStar_Syntax_Syntax.Tm_fvar fv ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_V1_Data.Tv_FVar fv)
           | FStar_Syntax_Syntax.Tm_uinst (t3, us) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     FStar_Compiler_Effect.op_Bar_Greater t3
                       FStar_Syntax_Subst.compress in
                   FStar_Compiler_Effect.op_Bar_Greater uu___4
                     FStar_Syntax_Util.unascribe in
                 uu___3.FStar_Syntax_Syntax.n in
               (match uu___2 with
                | FStar_Syntax_Syntax.Tm_fvar fv ->
                    FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                      (FStar_Reflection_V1_Data.Tv_UInst (fv, us))
                | uu___3 ->
                    failwith "Tac::inspect: Tm_uinst head not an fvar")
           | FStar_Syntax_Syntax.Tm_ascribed
               { FStar_Syntax_Syntax.tm = t3;
                 FStar_Syntax_Syntax.asc =
                   (FStar_Pervasives.Inl ty, tacopt, eq);
                 FStar_Syntax_Syntax.eff_opt = uu___2;_}
               ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_V1_Data.Tv_AscribedT (t3, ty, tacopt, eq))
           | FStar_Syntax_Syntax.Tm_ascribed
               { FStar_Syntax_Syntax.tm = t3;
                 FStar_Syntax_Syntax.asc =
                   (FStar_Pervasives.Inr cty, tacopt, eq);
                 FStar_Syntax_Syntax.eff_opt = uu___2;_}
               ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_V1_Data.Tv_AscribedC (t3, cty, tacopt, eq))
           | FStar_Syntax_Syntax.Tm_app
               { FStar_Syntax_Syntax.hd = uu___2;
                 FStar_Syntax_Syntax.args = [];_}
               -> failwith "empty arguments on Tm_app"
           | FStar_Syntax_Syntax.Tm_app
               { FStar_Syntax_Syntax.hd = hd;
                 FStar_Syntax_Syntax.args = args;_}
               ->
               let uu___2 = last args in
               (match uu___2 with
                | (a, q) ->
                    let q' = FStar_Reflection_V1_Builtins.inspect_aqual q in
                    let uu___3 =
                      let uu___4 =
                        let uu___5 =
                          let uu___6 = init args in
                          FStar_Syntax_Syntax.mk_Tm_app hd uu___6
                            t2.FStar_Syntax_Syntax.pos in
                        (uu___5, (a, q')) in
                      FStar_Reflection_V1_Data.Tv_App uu___4 in
                    FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                      uu___3)
           | FStar_Syntax_Syntax.Tm_abs
               { FStar_Syntax_Syntax.bs = [];
                 FStar_Syntax_Syntax.body = uu___2;
                 FStar_Syntax_Syntax.rc_opt = uu___3;_}
               -> failwith "empty arguments on Tm_abs"
           | FStar_Syntax_Syntax.Tm_abs
               { FStar_Syntax_Syntax.bs = bs; FStar_Syntax_Syntax.body = t3;
                 FStar_Syntax_Syntax.rc_opt = k;_}
               ->
               let uu___2 = FStar_Syntax_Subst.open_term bs t3 in
               (match uu___2 with
                | (bs1, t4) ->
                    (match bs1 with
                     | [] -> failwith "impossible"
                     | b::bs2 ->
                         let uu___3 =
                           let uu___4 =
                             let uu___5 = FStar_Syntax_Util.abs bs2 t4 k in
                             (b, uu___5) in
                           FStar_Reflection_V1_Data.Tv_Abs uu___4 in
                         FStar_Compiler_Effect.op_Less_Bar
                           FStar_Tactics_Monad.ret uu___3))
           | FStar_Syntax_Syntax.Tm_type u ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_V1_Data.Tv_Type u)
           | FStar_Syntax_Syntax.Tm_arrow
               { FStar_Syntax_Syntax.bs1 = [];
                 FStar_Syntax_Syntax.comp = uu___2;_}
               -> failwith "empty binders on arrow"
           | FStar_Syntax_Syntax.Tm_arrow uu___2 ->
               let uu___3 = FStar_Syntax_Util.arrow_one t2 in
               (match uu___3 with
                | FStar_Pervasives_Native.Some (b, c) ->
                    FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                      (FStar_Reflection_V1_Data.Tv_Arrow (b, c))
                | FStar_Pervasives_Native.None -> failwith "impossible")
           | FStar_Syntax_Syntax.Tm_refine
               { FStar_Syntax_Syntax.b = bv; FStar_Syntax_Syntax.phi = t3;_}
               ->
               let b = FStar_Syntax_Syntax.mk_binder bv in
               let uu___2 = FStar_Syntax_Subst.open_term [b] t3 in
               (match uu___2 with
                | (b', t4) ->
                    let b1 =
                      match b' with
                      | b'1::[] -> b'1
                      | uu___3 -> failwith "impossible" in
                    FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                      (FStar_Reflection_V1_Data.Tv_Refine
                         ((b1.FStar_Syntax_Syntax.binder_bv),
                           ((b1.FStar_Syntax_Syntax.binder_bv).FStar_Syntax_Syntax.sort),
                           t4)))
           | FStar_Syntax_Syntax.Tm_constant c ->
               let uu___2 =
                 let uu___3 = FStar_Reflection_V1_Builtins.inspect_const c in
                 FStar_Reflection_V1_Data.Tv_Const uu___3 in
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 uu___2
           | FStar_Syntax_Syntax.Tm_uvar (ctx_u, s) ->
               let uu___2 =
                 let uu___3 =
                   let uu___4 =
                     let uu___5 =
                       FStar_Syntax_Unionfind.uvar_unique_id
                         ctx_u.FStar_Syntax_Syntax.ctx_uvar_head in
                     FStar_BigInt.of_int_fs uu___5 in
                   (uu___4, (ctx_u, s)) in
                 FStar_Reflection_V1_Data.Tv_Uvar uu___3 in
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 uu___2
           | FStar_Syntax_Syntax.Tm_let
               { FStar_Syntax_Syntax.lbs = (false, lb::[]);
                 FStar_Syntax_Syntax.body1 = t21;_}
               ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                   FStar_Reflection_V1_Data.Tv_Unsupp
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Pervasives.Inr uu___3 ->
                      FStar_Compiler_Effect.op_Less_Bar
                        FStar_Tactics_Monad.ret
                        FStar_Reflection_V1_Data.Tv_Unsupp
                  | FStar_Pervasives.Inl bv ->
                      let b = FStar_Syntax_Syntax.mk_binder bv in
                      let uu___3 = FStar_Syntax_Subst.open_term [b] t21 in
                      (match uu___3 with
                       | (bs, t22) ->
                           let b1 =
                             match bs with
                             | b2::[] -> b2
                             | uu___4 ->
                                 failwith
                                   "impossible: open_term returned different amount of binders" in
                           FStar_Compiler_Effect.op_Less_Bar
                             FStar_Tactics_Monad.ret
                             (FStar_Reflection_V1_Data.Tv_Let
                                (false, (lb.FStar_Syntax_Syntax.lbattrs),
                                  (b1.FStar_Syntax_Syntax.binder_bv),
                                  (bv.FStar_Syntax_Syntax.sort),
                                  (lb.FStar_Syntax_Syntax.lbdef), t22))))
           | FStar_Syntax_Syntax.Tm_let
               { FStar_Syntax_Syntax.lbs = (true, lb::[]);
                 FStar_Syntax_Syntax.body1 = t21;_}
               ->
               if lb.FStar_Syntax_Syntax.lbunivs <> []
               then
                 FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                   FStar_Reflection_V1_Data.Tv_Unsupp
               else
                 (match lb.FStar_Syntax_Syntax.lbname with
                  | FStar_Pervasives.Inr uu___3 ->
                      FStar_Compiler_Effect.op_Less_Bar
                        FStar_Tactics_Monad.ret
                        FStar_Reflection_V1_Data.Tv_Unsupp
                  | FStar_Pervasives.Inl bv ->
                      let uu___3 = FStar_Syntax_Subst.open_let_rec [lb] t21 in
                      (match uu___3 with
                       | (lbs, t22) ->
                           (match lbs with
                            | lb1::[] ->
                                (match lb1.FStar_Syntax_Syntax.lbname with
                                 | FStar_Pervasives.Inr uu___4 ->
                                     FStar_Tactics_Monad.ret
                                       FStar_Reflection_V1_Data.Tv_Unsupp
                                 | FStar_Pervasives.Inl bv1 ->
                                     FStar_Compiler_Effect.op_Less_Bar
                                       FStar_Tactics_Monad.ret
                                       (FStar_Reflection_V1_Data.Tv_Let
                                          (true,
                                            (lb1.FStar_Syntax_Syntax.lbattrs),
                                            bv1,
                                            (bv1.FStar_Syntax_Syntax.sort),
                                            (lb1.FStar_Syntax_Syntax.lbdef),
                                            t22)))
                            | uu___4 ->
                                failwith
                                  "impossible: open_term returned different amount of binders")))
           | FStar_Syntax_Syntax.Tm_match
               { FStar_Syntax_Syntax.scrutinee = t3;
                 FStar_Syntax_Syntax.ret_opt = ret_opt;
                 FStar_Syntax_Syntax.brs = brs;
                 FStar_Syntax_Syntax.rc_opt1 = uu___2;_}
               ->
               let rec inspect_pat p =
                 match p.FStar_Syntax_Syntax.v with
                 | FStar_Syntax_Syntax.Pat_constant c ->
                     let uu___3 =
                       FStar_Reflection_V1_Builtins.inspect_const c in
                     FStar_Reflection_V1_Data.Pat_Constant uu___3
                 | FStar_Syntax_Syntax.Pat_cons (fv, us_opt, ps) ->
                     let uu___3 =
                       let uu___4 =
                         FStar_Compiler_List.map
                           (fun uu___5 ->
                              match uu___5 with
                              | (p1, b) ->
                                  let uu___6 = inspect_pat p1 in (uu___6, b))
                           ps in
                       (fv, us_opt, uu___4) in
                     FStar_Reflection_V1_Data.Pat_Cons uu___3
                 | FStar_Syntax_Syntax.Pat_var bv ->
                     FStar_Reflection_V1_Data.Pat_Var
                       (bv, (bv.FStar_Syntax_Syntax.sort))
                 | FStar_Syntax_Syntax.Pat_dot_term eopt ->
                     FStar_Reflection_V1_Data.Pat_Dot_Term eopt in
               let brs1 =
                 FStar_Compiler_List.map FStar_Syntax_Subst.open_branch brs in
               let brs2 =
                 FStar_Compiler_List.map
                   (fun uu___3 ->
                      match uu___3 with
                      | (pat, uu___4, t4) ->
                          let uu___5 = inspect_pat pat in (uu___5, t4)) brs1 in
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 (FStar_Reflection_V1_Data.Tv_Match (t3, ret_opt, brs2))
           | FStar_Syntax_Syntax.Tm_unknown ->
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 FStar_Reflection_V1_Data.Tv_Unknown
           | uu___2 ->
               ((let uu___4 =
                   let uu___5 =
                     let uu___6 = FStar_Syntax_Print.tag_of_term t2 in
                     let uu___7 = FStar_Syntax_Print.term_to_string t2 in
                     FStar_Compiler_Util.format2
                       "inspect: outside of expected syntax (%s, %s)\n"
                       uu___6 uu___7 in
                   (FStar_Errors_Codes.Warning_CantInspect, uu___5) in
                 FStar_Errors.log_issue t2.FStar_Syntax_Syntax.pos uu___4);
                FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                  FStar_Reflection_V1_Data.Tv_Unsupp)) in
    FStar_Tactics_Monad.wrap_err "inspect" uu___
let (pack' :
  FStar_Reflection_V1_Data.term_view ->
    Prims.bool -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun tv ->
    fun leave_curried ->
      match tv with
      | FStar_Reflection_V1_Data.Tv_Var bv ->
          let uu___ = FStar_Syntax_Syntax.bv_to_name bv in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_BVar bv ->
          let uu___ = FStar_Syntax_Syntax.bv_to_tm bv in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_FVar fv ->
          let uu___ = FStar_Syntax_Syntax.fv_to_tm fv in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_UInst (fv, us) ->
          let uu___ =
            let uu___1 = FStar_Syntax_Syntax.fv_to_tm fv in
            FStar_Syntax_Syntax.mk_Tm_uinst uu___1 us in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_App (l, (r, q)) ->
          let q' = FStar_Reflection_V1_Builtins.pack_aqual q in
          let uu___ = FStar_Syntax_Util.mk_app l [(r, q')] in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Abs (b, t) ->
          let uu___ =
            FStar_Syntax_Util.abs [b] t FStar_Pervasives_Native.None in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Arrow (b, c) ->
          let uu___ =
            if leave_curried
            then FStar_Syntax_Util.arrow [b] c
            else
              (let uu___2 = FStar_Syntax_Util.arrow [b] c in
               FStar_Syntax_Util.canon_arrow uu___2) in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Type u ->
          let uu___ =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_type u)
              FStar_Compiler_Range_Type.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Refine (bv, sort, t) ->
          let bv1 =
            {
              FStar_Syntax_Syntax.ppname = (bv.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = sort
            } in
          let uu___ = FStar_Syntax_Util.refine bv1 t in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Const c ->
          let uu___ =
            let uu___1 =
              let uu___2 = FStar_Reflection_V1_Builtins.pack_const c in
              FStar_Syntax_Syntax.Tm_constant uu___2 in
            FStar_Syntax_Syntax.mk uu___1
              FStar_Compiler_Range_Type.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Uvar (_u, ctx_u_s) ->
          let uu___ =
            FStar_Syntax_Syntax.mk (FStar_Syntax_Syntax.Tm_uvar ctx_u_s)
              FStar_Compiler_Range_Type.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Let (false, attrs, bv, ty, t1, t2) ->
          let bv1 =
            {
              FStar_Syntax_Syntax.ppname = (bv.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = ty
            } in
          let lb =
            FStar_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl bv1) []
              bv1.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid
              t1 attrs FStar_Compiler_Range_Type.dummyRange in
          let uu___ =
            let uu___1 =
              let uu___2 =
                let uu___3 =
                  let uu___4 =
                    let uu___5 = FStar_Syntax_Syntax.mk_binder bv1 in
                    [uu___5] in
                  FStar_Syntax_Subst.close uu___4 t2 in
                {
                  FStar_Syntax_Syntax.lbs = (false, [lb]);
                  FStar_Syntax_Syntax.body1 = uu___3
                } in
              FStar_Syntax_Syntax.Tm_let uu___2 in
            FStar_Syntax_Syntax.mk uu___1
              FStar_Compiler_Range_Type.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Let (true, attrs, bv, ty, t1, t2) ->
          let bv1 =
            {
              FStar_Syntax_Syntax.ppname = (bv.FStar_Syntax_Syntax.ppname);
              FStar_Syntax_Syntax.index = (bv.FStar_Syntax_Syntax.index);
              FStar_Syntax_Syntax.sort = ty
            } in
          let lb =
            FStar_Syntax_Util.mk_letbinding (FStar_Pervasives.Inl bv1) []
              bv1.FStar_Syntax_Syntax.sort FStar_Parser_Const.effect_Tot_lid
              t1 attrs FStar_Compiler_Range_Type.dummyRange in
          let uu___ = FStar_Syntax_Subst.close_let_rec [lb] t2 in
          (match uu___ with
           | (lbs, body) ->
               let uu___1 =
                 FStar_Syntax_Syntax.mk
                   (FStar_Syntax_Syntax.Tm_let
                      {
                        FStar_Syntax_Syntax.lbs = (true, lbs);
                        FStar_Syntax_Syntax.body1 = body
                      }) FStar_Compiler_Range_Type.dummyRange in
               FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret
                 uu___1)
      | FStar_Reflection_V1_Data.Tv_Match (t, ret_opt, brs) ->
          let wrap v =
            {
              FStar_Syntax_Syntax.v = v;
              FStar_Syntax_Syntax.p = FStar_Compiler_Range_Type.dummyRange
            } in
          let rec pack_pat p =
            match p with
            | FStar_Reflection_V1_Data.Pat_Constant c ->
                let uu___ =
                  let uu___1 = FStar_Reflection_V1_Builtins.pack_const c in
                  FStar_Syntax_Syntax.Pat_constant uu___1 in
                FStar_Compiler_Effect.op_Less_Bar wrap uu___
            | FStar_Reflection_V1_Data.Pat_Cons (fv, us_opt, ps) ->
                let uu___ =
                  let uu___1 =
                    let uu___2 =
                      FStar_Compiler_List.map
                        (fun uu___3 ->
                           match uu___3 with
                           | (p1, b) ->
                               let uu___4 = pack_pat p1 in (uu___4, b)) ps in
                    (fv, us_opt, uu___2) in
                  FStar_Syntax_Syntax.Pat_cons uu___1 in
                FStar_Compiler_Effect.op_Less_Bar wrap uu___
            | FStar_Reflection_V1_Data.Pat_Var (bv, _sort) ->
                FStar_Compiler_Effect.op_Less_Bar wrap
                  (FStar_Syntax_Syntax.Pat_var bv)
            | FStar_Reflection_V1_Data.Pat_Dot_Term eopt ->
                FStar_Compiler_Effect.op_Less_Bar wrap
                  (FStar_Syntax_Syntax.Pat_dot_term eopt) in
          let brs1 =
            FStar_Compiler_List.map
              (fun uu___ ->
                 match uu___ with
                 | (pat, t1) ->
                     let uu___1 = pack_pat pat in
                     (uu___1, FStar_Pervasives_Native.None, t1)) brs in
          let brs2 =
            FStar_Compiler_List.map FStar_Syntax_Subst.close_branch brs1 in
          let uu___ =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_match
                 {
                   FStar_Syntax_Syntax.scrutinee = t;
                   FStar_Syntax_Syntax.ret_opt = ret_opt;
                   FStar_Syntax_Syntax.brs = brs2;
                   FStar_Syntax_Syntax.rc_opt1 = FStar_Pervasives_Native.None
                 }) FStar_Compiler_Range_Type.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_AscribedT (e, t, tacopt, use_eq) ->
          let uu___ =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_ascribed
                 {
                   FStar_Syntax_Syntax.tm = e;
                   FStar_Syntax_Syntax.asc =
                     ((FStar_Pervasives.Inl t), tacopt, use_eq);
                   FStar_Syntax_Syntax.eff_opt = FStar_Pervasives_Native.None
                 }) FStar_Compiler_Range_Type.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_AscribedC (e, c, tacopt, use_eq) ->
          let uu___ =
            FStar_Syntax_Syntax.mk
              (FStar_Syntax_Syntax.Tm_ascribed
                 {
                   FStar_Syntax_Syntax.tm = e;
                   FStar_Syntax_Syntax.asc =
                     ((FStar_Pervasives.Inr c), tacopt, use_eq);
                   FStar_Syntax_Syntax.eff_opt = FStar_Pervasives_Native.None
                 }) FStar_Compiler_Range_Type.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Unknown ->
          let uu___ =
            FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
              FStar_Compiler_Range_Type.dummyRange in
          FStar_Compiler_Effect.op_Less_Bar FStar_Tactics_Monad.ret uu___
      | FStar_Reflection_V1_Data.Tv_Unsupp ->
          FStar_Tactics_Monad.fail "cannot pack Tv_Unsupp"
let (pack :
  FStar_Reflection_V1_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  = fun tv -> pack' tv false
let (pack_curried :
  FStar_Reflection_V1_Data.term_view ->
    FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  = fun tv -> pack' tv true
let (lget :
  FStar_Syntax_Syntax.typ ->
    Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac)
  =
  fun ty ->
    fun k ->
      let uu___ =
        FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
          (fun ps ->
             let uu___1 =
               FStar_Compiler_Util.psmap_try_find
                 ps.FStar_Tactics_Types.local_state k in
             match uu___1 with
             | FStar_Pervasives_Native.None ->
                 FStar_Tactics_Monad.fail "not found"
             | FStar_Pervasives_Native.Some t -> unquote ty t) in
      FStar_Compiler_Effect.op_Less_Bar (FStar_Tactics_Monad.wrap_err "lget")
        uu___
let (lset :
  FStar_Syntax_Syntax.typ ->
    Prims.string -> FStar_Syntax_Syntax.term -> unit FStar_Tactics_Monad.tac)
  =
  fun _ty ->
    fun k ->
      fun t ->
        let uu___ =
          FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
            (fun ps ->
               let ps1 =
                 let uu___1 =
                   FStar_Compiler_Util.psmap_add
                     ps.FStar_Tactics_Types.local_state k t in
                 {
                   FStar_Tactics_Types.main_context =
                     (ps.FStar_Tactics_Types.main_context);
                   FStar_Tactics_Types.all_implicits =
                     (ps.FStar_Tactics_Types.all_implicits);
                   FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
                   FStar_Tactics_Types.smt_goals =
                     (ps.FStar_Tactics_Types.smt_goals);
                   FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
                   FStar_Tactics_Types.__dump =
                     (ps.FStar_Tactics_Types.__dump);
                   FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
                   FStar_Tactics_Types.entry_range =
                     (ps.FStar_Tactics_Types.entry_range);
                   FStar_Tactics_Types.guard_policy =
                     (ps.FStar_Tactics_Types.guard_policy);
                   FStar_Tactics_Types.freshness =
                     (ps.FStar_Tactics_Types.freshness);
                   FStar_Tactics_Types.tac_verb_dbg =
                     (ps.FStar_Tactics_Types.tac_verb_dbg);
                   FStar_Tactics_Types.local_state = uu___1;
                   FStar_Tactics_Types.urgency =
                     (ps.FStar_Tactics_Types.urgency)
                 } in
               FStar_Tactics_Monad.set ps1) in
        FStar_Compiler_Effect.op_Less_Bar
          (FStar_Tactics_Monad.wrap_err "lset") uu___
let (set_urgency : FStar_BigInt.t -> unit FStar_Tactics_Monad.tac) =
  fun u ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.get
      (fun ps ->
         let ps1 =
           let uu___ = FStar_BigInt.to_int_fs u in
           {
             FStar_Tactics_Types.main_context =
               (ps.FStar_Tactics_Types.main_context);
             FStar_Tactics_Types.all_implicits =
               (ps.FStar_Tactics_Types.all_implicits);
             FStar_Tactics_Types.goals = (ps.FStar_Tactics_Types.goals);
             FStar_Tactics_Types.smt_goals =
               (ps.FStar_Tactics_Types.smt_goals);
             FStar_Tactics_Types.depth = (ps.FStar_Tactics_Types.depth);
             FStar_Tactics_Types.__dump = (ps.FStar_Tactics_Types.__dump);
             FStar_Tactics_Types.psc = (ps.FStar_Tactics_Types.psc);
             FStar_Tactics_Types.entry_range =
               (ps.FStar_Tactics_Types.entry_range);
             FStar_Tactics_Types.guard_policy =
               (ps.FStar_Tactics_Types.guard_policy);
             FStar_Tactics_Types.freshness =
               (ps.FStar_Tactics_Types.freshness);
             FStar_Tactics_Types.tac_verb_dbg =
               (ps.FStar_Tactics_Types.tac_verb_dbg);
             FStar_Tactics_Types.local_state =
               (ps.FStar_Tactics_Types.local_state);
             FStar_Tactics_Types.urgency = uu___
           } in
         FStar_Tactics_Monad.set ps1)
let (t_commute_applied_match : unit -> unit FStar_Tactics_Monad.tac) =
  fun uu___ ->
    let uu___1 =
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
        (fun g ->
           let uu___2 =
             let uu___3 = FStar_Tactics_Types.goal_env g in
             let uu___4 = FStar_Tactics_Types.goal_type g in
             destruct_eq uu___3 uu___4 in
           match uu___2 with
           | FStar_Pervasives_Native.Some (l, r) ->
               let uu___3 = FStar_Syntax_Util.head_and_args_full l in
               (match uu___3 with
                | (lh, las) ->
                    let uu___4 =
                      let uu___5 =
                        let uu___6 = FStar_Syntax_Util.unascribe lh in
                        FStar_Syntax_Subst.compress uu___6 in
                      uu___5.FStar_Syntax_Syntax.n in
                    (match uu___4 with
                     | FStar_Syntax_Syntax.Tm_match
                         { FStar_Syntax_Syntax.scrutinee = e;
                           FStar_Syntax_Syntax.ret_opt = asc_opt;
                           FStar_Syntax_Syntax.brs = brs;
                           FStar_Syntax_Syntax.rc_opt1 = lopt;_}
                         ->
                         let brs' =
                           FStar_Compiler_List.map
                             (fun uu___5 ->
                                match uu___5 with
                                | (p, w, e1) ->
                                    let uu___6 =
                                      FStar_Syntax_Util.mk_app e1 las in
                                    (p, w, uu___6)) brs in
                         let lopt' =
                           FStar_Compiler_Effect.op_Bar_Greater lopt
                             (FStar_Compiler_Util.map_option
                                (fun rc ->
                                   let uu___5 =
                                     FStar_Compiler_Effect.op_Bar_Greater
                                       rc.FStar_Syntax_Syntax.residual_typ
                                       (FStar_Compiler_Util.map_option
                                          (fun t ->
                                             let uu___6 =
                                               let uu___7 =
                                                 FStar_Tactics_Types.goal_env
                                                   g in
                                               FStar_TypeChecker_Normalize.get_n_binders
                                                 uu___7
                                                 (FStar_Compiler_List.length
                                                    las) t in
                                             match uu___6 with
                                             | (bs, c) ->
                                                 let uu___7 =
                                                   FStar_Syntax_Subst.open_comp
                                                     bs c in
                                                 (match uu___7 with
                                                  | (bs1, c1) ->
                                                      let ss =
                                                        FStar_Compiler_List.map2
                                                          (fun b ->
                                                             fun a ->
                                                               FStar_Syntax_Syntax.NT
                                                                 ((b.FStar_Syntax_Syntax.binder_bv),
                                                                   (FStar_Pervasives_Native.fst
                                                                    a))) bs1
                                                          las in
                                                      let c2 =
                                                        FStar_Syntax_Subst.subst_comp
                                                          ss c1 in
                                                      FStar_Syntax_Util.comp_result
                                                        c2))) in
                                   {
                                     FStar_Syntax_Syntax.residual_effect =
                                       (rc.FStar_Syntax_Syntax.residual_effect);
                                     FStar_Syntax_Syntax.residual_typ =
                                       uu___5;
                                     FStar_Syntax_Syntax.residual_flags =
                                       (rc.FStar_Syntax_Syntax.residual_flags)
                                   })) in
                         let l' =
                           FStar_Syntax_Syntax.mk
                             (FStar_Syntax_Syntax.Tm_match
                                {
                                  FStar_Syntax_Syntax.scrutinee = e;
                                  FStar_Syntax_Syntax.ret_opt = asc_opt;
                                  FStar_Syntax_Syntax.brs = brs';
                                  FStar_Syntax_Syntax.rc_opt1 = lopt'
                                }) l.FStar_Syntax_Syntax.pos in
                         let must_tot = true in
                         let uu___5 =
                           let uu___6 = FStar_Tactics_Types.goal_env g in
                           do_unify_maybe_guards false must_tot uu___6 l' r in
                         FStar_Tactics_Monad.op_let_Bang uu___5
                           (fun uu___6 ->
                              match uu___6 with
                              | FStar_Pervasives_Native.None ->
                                  FStar_Tactics_Monad.fail
                                    "discharging the equality failed"
                              | FStar_Pervasives_Native.Some guard ->
                                  let uu___7 =
                                    FStar_TypeChecker_Env.is_trivial_guard_formula
                                      guard in
                                  if uu___7
                                  then
                                    (mark_uvar_as_already_checked
                                       g.FStar_Tactics_Types.goal_ctx_uvar;
                                     solve g FStar_Syntax_Util.exp_unit)
                                  else
                                    failwith
                                      "internal error: _t_refl: guard is not trivial")
                     | uu___5 ->
                         FStar_Tactics_Monad.fail "lhs is not a match"))
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "not an equality") in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "t_commute_applied_match") uu___1
let (string_to_term :
  env -> Prims.string -> FStar_Syntax_Syntax.term FStar_Tactics_Monad.tac) =
  fun e ->
    fun s ->
      let frag_of_text s1 =
        {
          FStar_Parser_ParseIt.frag_fname = "<string_of_term>";
          FStar_Parser_ParseIt.frag_text = s1;
          FStar_Parser_ParseIt.frag_line = Prims.int_one;
          FStar_Parser_ParseIt.frag_col = Prims.int_zero
        } in
      let uu___ =
        FStar_Parser_ParseIt.parse
          (FStar_Parser_ParseIt.Fragment (frag_of_text s)) in
      match uu___ with
      | FStar_Parser_ParseIt.Term t ->
          let dsenv =
            let uu___1 = FStar_TypeChecker_Env.current_module e in
            FStar_Syntax_DsEnv.set_current_module
              e.FStar_TypeChecker_Env.dsenv uu___1 in
          (try
             (fun uu___1 ->
                match () with
                | () ->
                    let uu___2 = FStar_ToSyntax_ToSyntax.desugar_term dsenv t in
                    FStar_Tactics_Monad.ret uu___2) ()
           with
           | FStar_Errors.Error (uu___2, e1, uu___3, uu___4) ->
               let uu___5 =
                 let uu___6 = FStar_Errors_Msg.rendermsg e1 in
                 Prims.op_Hat "string_of_term: " uu___6 in
               FStar_Tactics_Monad.fail uu___5
           | uu___2 ->
               FStar_Tactics_Monad.fail "string_of_term: Unknown error")
      | FStar_Parser_ParseIt.ASTFragment uu___1 ->
          FStar_Tactics_Monad.fail
            "string_of_term: expected a Term as a result, got an ASTFragment"
      | FStar_Parser_ParseIt.ParseError (uu___1, err, uu___2) ->
          let uu___3 =
            let uu___4 = FStar_Errors_Msg.rendermsg err in
            Prims.op_Hat "string_of_term: got error " uu___4 in
          FStar_Tactics_Monad.fail uu___3
let (push_bv_dsenv :
  env ->
    Prims.string -> (env * FStar_Syntax_Syntax.bv) FStar_Tactics_Monad.tac)
  =
  fun e ->
    fun i ->
      let ident =
        FStar_Ident.mk_ident (i, FStar_Compiler_Range_Type.dummyRange) in
      let uu___ =
        FStar_Syntax_DsEnv.push_bv e.FStar_TypeChecker_Env.dsenv ident in
      match uu___ with
      | (dsenv, bv) ->
          FStar_Tactics_Monad.ret
            ({
               FStar_TypeChecker_Env.solver =
                 (e.FStar_TypeChecker_Env.solver);
               FStar_TypeChecker_Env.range = (e.FStar_TypeChecker_Env.range);
               FStar_TypeChecker_Env.curmodule =
                 (e.FStar_TypeChecker_Env.curmodule);
               FStar_TypeChecker_Env.gamma = (e.FStar_TypeChecker_Env.gamma);
               FStar_TypeChecker_Env.gamma_sig =
                 (e.FStar_TypeChecker_Env.gamma_sig);
               FStar_TypeChecker_Env.gamma_cache =
                 (e.FStar_TypeChecker_Env.gamma_cache);
               FStar_TypeChecker_Env.modules =
                 (e.FStar_TypeChecker_Env.modules);
               FStar_TypeChecker_Env.expected_typ =
                 (e.FStar_TypeChecker_Env.expected_typ);
               FStar_TypeChecker_Env.sigtab =
                 (e.FStar_TypeChecker_Env.sigtab);
               FStar_TypeChecker_Env.attrtab =
                 (e.FStar_TypeChecker_Env.attrtab);
               FStar_TypeChecker_Env.instantiate_imp =
                 (e.FStar_TypeChecker_Env.instantiate_imp);
               FStar_TypeChecker_Env.effects =
                 (e.FStar_TypeChecker_Env.effects);
               FStar_TypeChecker_Env.generalize =
                 (e.FStar_TypeChecker_Env.generalize);
               FStar_TypeChecker_Env.letrecs =
                 (e.FStar_TypeChecker_Env.letrecs);
               FStar_TypeChecker_Env.top_level =
                 (e.FStar_TypeChecker_Env.top_level);
               FStar_TypeChecker_Env.check_uvars =
                 (e.FStar_TypeChecker_Env.check_uvars);
               FStar_TypeChecker_Env.use_eq_strict =
                 (e.FStar_TypeChecker_Env.use_eq_strict);
               FStar_TypeChecker_Env.is_iface =
                 (e.FStar_TypeChecker_Env.is_iface);
               FStar_TypeChecker_Env.admit = (e.FStar_TypeChecker_Env.admit);
               FStar_TypeChecker_Env.lax = (e.FStar_TypeChecker_Env.lax);
               FStar_TypeChecker_Env.lax_universes =
                 (e.FStar_TypeChecker_Env.lax_universes);
               FStar_TypeChecker_Env.phase1 =
                 (e.FStar_TypeChecker_Env.phase1);
               FStar_TypeChecker_Env.failhard =
                 (e.FStar_TypeChecker_Env.failhard);
               FStar_TypeChecker_Env.nosynth =
                 (e.FStar_TypeChecker_Env.nosynth);
               FStar_TypeChecker_Env.uvar_subtyping =
                 (e.FStar_TypeChecker_Env.uvar_subtyping);
               FStar_TypeChecker_Env.intactics =
                 (e.FStar_TypeChecker_Env.intactics);
               FStar_TypeChecker_Env.nocoerce =
                 (e.FStar_TypeChecker_Env.nocoerce);
               FStar_TypeChecker_Env.tc_term =
                 (e.FStar_TypeChecker_Env.tc_term);
               FStar_TypeChecker_Env.typeof_tot_or_gtot_term =
                 (e.FStar_TypeChecker_Env.typeof_tot_or_gtot_term);
               FStar_TypeChecker_Env.universe_of =
                 (e.FStar_TypeChecker_Env.universe_of);
               FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term =
                 (e.FStar_TypeChecker_Env.typeof_well_typed_tot_or_gtot_term);
               FStar_TypeChecker_Env.teq_nosmt_force =
                 (e.FStar_TypeChecker_Env.teq_nosmt_force);
               FStar_TypeChecker_Env.subtype_nosmt_force =
                 (e.FStar_TypeChecker_Env.subtype_nosmt_force);
               FStar_TypeChecker_Env.qtbl_name_and_index =
                 (e.FStar_TypeChecker_Env.qtbl_name_and_index);
               FStar_TypeChecker_Env.normalized_eff_names =
                 (e.FStar_TypeChecker_Env.normalized_eff_names);
               FStar_TypeChecker_Env.fv_delta_depths =
                 (e.FStar_TypeChecker_Env.fv_delta_depths);
               FStar_TypeChecker_Env.proof_ns =
                 (e.FStar_TypeChecker_Env.proof_ns);
               FStar_TypeChecker_Env.synth_hook =
                 (e.FStar_TypeChecker_Env.synth_hook);
               FStar_TypeChecker_Env.try_solve_implicits_hook =
                 (e.FStar_TypeChecker_Env.try_solve_implicits_hook);
               FStar_TypeChecker_Env.splice =
                 (e.FStar_TypeChecker_Env.splice);
               FStar_TypeChecker_Env.mpreprocess =
                 (e.FStar_TypeChecker_Env.mpreprocess);
               FStar_TypeChecker_Env.postprocess =
                 (e.FStar_TypeChecker_Env.postprocess);
               FStar_TypeChecker_Env.identifier_info =
                 (e.FStar_TypeChecker_Env.identifier_info);
               FStar_TypeChecker_Env.tc_hooks =
                 (e.FStar_TypeChecker_Env.tc_hooks);
               FStar_TypeChecker_Env.dsenv = dsenv;
               FStar_TypeChecker_Env.nbe = (e.FStar_TypeChecker_Env.nbe);
               FStar_TypeChecker_Env.strict_args_tab =
                 (e.FStar_TypeChecker_Env.strict_args_tab);
               FStar_TypeChecker_Env.erasable_types_tab =
                 (e.FStar_TypeChecker_Env.erasable_types_tab);
               FStar_TypeChecker_Env.enable_defer_to_tac =
                 (e.FStar_TypeChecker_Env.enable_defer_to_tac);
               FStar_TypeChecker_Env.unif_allow_ref_guards =
                 (e.FStar_TypeChecker_Env.unif_allow_ref_guards);
               FStar_TypeChecker_Env.erase_erasable_args =
                 (e.FStar_TypeChecker_Env.erase_erasable_args);
               FStar_TypeChecker_Env.core_check =
                 (e.FStar_TypeChecker_Env.core_check)
             }, bv)
let (term_to_string :
  FStar_Syntax_Syntax.term -> Prims.string FStar_Tactics_Monad.tac) =
  fun t ->
    let s = FStar_Syntax_Print.term_to_string t in FStar_Tactics_Monad.ret s
let (comp_to_string :
  FStar_Syntax_Syntax.comp -> Prims.string FStar_Tactics_Monad.tac) =
  fun c ->
    let s = FStar_Syntax_Print.comp_to_string c in FStar_Tactics_Monad.ret s
let (range_to_string :
  FStar_Compiler_Range_Type.range -> Prims.string FStar_Tactics_Monad.tac) =
  fun r ->
    let uu___ = FStar_Compiler_Range_Ops.string_of_range r in
    FStar_Tactics_Monad.ret uu___
let (term_eq_old :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.term -> Prims.bool FStar_Tactics_Monad.tac)
  =
  fun t1 ->
    fun t2 ->
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.idtac
        (fun uu___ ->
           let uu___1 = FStar_Syntax_Util.term_eq t1 t2 in
           FStar_Tactics_Monad.ret uu___1)
let with_compat_pre_core :
  'a .
    FStar_BigInt.t ->
      'a FStar_Tactics_Monad.tac -> 'a FStar_Tactics_Monad.tac
  =
  fun n ->
    fun f ->
      FStar_Tactics_Monad.mk_tac
        (fun ps ->
           FStar_Options.with_saved_options
             (fun uu___ ->
                let _res = FStar_Options.set_options "--compat_pre_core 0" in
                FStar_Tactics_Monad.run f ps))
let (get_vconfig : unit -> FStar_VConfig.vconfig FStar_Tactics_Monad.tac) =
  fun uu___ ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun g ->
         let vcfg =
           FStar_Options.with_saved_options
             (fun uu___1 ->
                (let uu___3 =
                   FStar_Compiler_Util.smap_copy g.FStar_Tactics_Types.opts in
                 FStar_Options.set uu___3);
                FStar_Options.get_vconfig ()) in
         FStar_Tactics_Monad.ret vcfg)
let (set_vconfig : FStar_VConfig.vconfig -> unit FStar_Tactics_Monad.tac) =
  fun vcfg ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
      (fun g ->
         let opts' =
           FStar_Options.with_saved_options
             (fun uu___ ->
                (let uu___2 =
                   FStar_Compiler_Util.smap_copy g.FStar_Tactics_Types.opts in
                 FStar_Options.set uu___2);
                FStar_Options.set_vconfig vcfg;
                FStar_Options.peek ()) in
         let g' =
           {
             FStar_Tactics_Types.goal_main_env =
               (g.FStar_Tactics_Types.goal_main_env);
             FStar_Tactics_Types.goal_ctx_uvar =
               (g.FStar_Tactics_Types.goal_ctx_uvar);
             FStar_Tactics_Types.opts = opts';
             FStar_Tactics_Types.is_guard = (g.FStar_Tactics_Types.is_guard);
             FStar_Tactics_Types.label = (g.FStar_Tactics_Types.label)
           } in
         FStar_Tactics_Monad.replace_cur g')
let (t_smt_sync : FStar_VConfig.vconfig -> unit FStar_Tactics_Monad.tac) =
  fun vcfg ->
    let uu___ =
      FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.cur_goal
        (fun goal ->
           let uu___1 = FStar_Tactics_Types.get_phi goal in
           match uu___1 with
           | FStar_Pervasives_Native.None ->
               FStar_Tactics_Monad.fail "Goal is not irrelevant"
           | FStar_Pervasives_Native.Some phi ->
               let e = FStar_Tactics_Types.goal_env goal in
               let ans =
                 FStar_Options.with_saved_options
                   (fun uu___2 ->
                      FStar_Options.set_vconfig vcfg;
                      (e.FStar_TypeChecker_Env.solver).FStar_TypeChecker_Env.solve_sync
                        FStar_Pervasives_Native.None e phi) in
               if ans
               then
                 (mark_uvar_as_already_checked
                    goal.FStar_Tactics_Types.goal_ctx_uvar;
                  solve goal FStar_Syntax_Util.exp_unit)
               else FStar_Tactics_Monad.fail "SMT did not solve this goal") in
    FStar_Compiler_Effect.op_Less_Bar
      (FStar_Tactics_Monad.wrap_err "t_smt_sync") uu___
let (free_uvars :
  FStar_Syntax_Syntax.term ->
    FStar_BigInt.t Prims.list FStar_Tactics_Monad.tac)
  =
  fun tm ->
    FStar_Tactics_Monad.op_let_Bang FStar_Tactics_Monad.idtac
      (fun uu___ ->
         let uvs =
           let uu___1 =
             let uu___2 = FStar_Syntax_Free.uvars_uncached tm in
             FStar_Compiler_Effect.op_Bar_Greater uu___2
               FStar_Compiler_Util.set_elements in
           FStar_Compiler_Effect.op_Bar_Greater uu___1
             (FStar_Compiler_List.map
                (fun u ->
                   let uu___2 =
                     FStar_Syntax_Unionfind.uvar_id
                       u.FStar_Syntax_Syntax.ctx_uvar_head in
                   FStar_BigInt.of_int_fs uu___2)) in
         FStar_Tactics_Monad.ret uvs)
let (dbg_refl : env -> (unit -> Prims.string) -> unit) =
  fun g ->
    fun msg ->
      let uu___ =
        FStar_Compiler_Effect.op_Less_Bar (FStar_TypeChecker_Env.debug g)
          (FStar_Options.Other "ReflTc") in
      if uu___
      then let uu___1 = msg () in FStar_Compiler_Util.print_string uu___1
      else ()
type issues = FStar_Errors.issue Prims.list
let refl_typing_builtin_wrapper :
  'a .
    (unit -> 'a) ->
      ('a FStar_Pervasives_Native.option * issues) FStar_Tactics_Monad.tac
  =
  fun f ->
    let tx = FStar_Syntax_Unionfind.new_transaction () in
    let uu___ =
      try
        (fun uu___1 ->
           match () with | () -> FStar_Errors.catch_errors_and_ignore_rest f)
          ()
      with
      | uu___1 ->
          let issue =
            let uu___2 =
              let uu___3 = FStar_Compiler_Util.print_exn uu___1 in
              FStar_Errors_Msg.mkmsg uu___3 in
            let uu___3 = FStar_Errors.get_ctx () in
            {
              FStar_Errors.issue_msg = uu___2;
              FStar_Errors.issue_level = FStar_Errors.EError;
              FStar_Errors.issue_range = FStar_Pervasives_Native.None;
              FStar_Errors.issue_number =
                (FStar_Pervasives_Native.Some (Prims.of_int (17)));
              FStar_Errors.issue_ctx = uu___3
            } in
          ([issue], FStar_Pervasives_Native.None) in
    match uu___ with
    | (errs, r) ->
        (FStar_Syntax_Unionfind.rollback tx;
         if (FStar_Compiler_List.length errs) > Prims.int_zero
         then FStar_Tactics_Monad.ret (FStar_Pervasives_Native.None, errs)
         else FStar_Tactics_Monad.ret (r, errs))
let (no_uvars_in_term : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t ->
    (let uu___ =
       FStar_Compiler_Effect.op_Bar_Greater t FStar_Syntax_Free.uvars in
     FStar_Compiler_Effect.op_Bar_Greater uu___
       FStar_Compiler_Util.set_is_empty)
      &&
      (let uu___ =
         FStar_Compiler_Effect.op_Bar_Greater t FStar_Syntax_Free.univs in
       FStar_Compiler_Effect.op_Bar_Greater uu___
         FStar_Compiler_Util.set_is_empty)
let (no_uvars_in_g : env -> Prims.bool) =
  fun g ->
    FStar_Compiler_Effect.op_Bar_Greater g.FStar_TypeChecker_Env.gamma
      (FStar_Compiler_Util.for_all
         (fun uu___ ->
            match uu___ with
            | FStar_Syntax_Syntax.Binding_var bv ->
                no_uvars_in_term bv.FStar_Syntax_Syntax.sort
            | uu___1 -> true))
type relation =
  | Subtyping 
  | Equality 
let (uu___is_Subtyping : relation -> Prims.bool) =
  fun projectee -> match projectee with | Subtyping -> true | uu___ -> false
let (uu___is_Equality : relation -> Prims.bool) =
  fun projectee -> match projectee with | Equality -> true | uu___ -> false
let (unexpected_uvars_issue :
  FStar_Compiler_Range_Type.range -> FStar_Errors.issue) =
  fun r ->
    let i =
      let uu___ = FStar_Errors_Msg.mkmsg "Cannot check relation with uvars" in
      let uu___1 =
        let uu___2 =
          FStar_Errors.errno
            FStar_Errors_Codes.Error_UnexpectedUnresolvedUvar in
        FStar_Pervasives_Native.Some uu___2 in
      {
        FStar_Errors.issue_msg = uu___;
        FStar_Errors.issue_level = FStar_Errors.EError;
        FStar_Errors.issue_range = (FStar_Pervasives_Native.Some r);
        FStar_Errors.issue_number = uu___1;
        FStar_Errors.issue_ctx = []
      } in
    i