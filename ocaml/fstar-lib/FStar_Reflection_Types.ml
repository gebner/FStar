open FStar_All

type binder  = FStar_Syntax_Syntax.binder
type bv      = FStar_Syntax_Syntax.bv
type namedv  = bv
type term    = FStar_Syntax_Syntax.term
type env     = FStar_TypeChecker_Env.env
type fv      = FStar_Syntax_Syntax.fv
type comp    = FStar_Syntax_Syntax.comp
type sigelt  = FStar_Syntax_Syntax.sigelt
type ctx_uvar_and_subst = FStar_Syntax_Syntax.ctx_uvar_and_subst
type optionstate = FStar_Options.optionstate
type letbinding = FStar_Syntax_Syntax.letbinding

type universe_uvar = FStar_Syntax_Syntax.universe_uvar
type universe = FStar_Syntax_Syntax.universe

type name        = string list
type ident       = FStar_Ident.ident
type univ_name   = ident
type typ         = term
type binders     = binder list
type match_returns_ascription = FStar_Syntax_Syntax.match_returns_ascription
type decls = sigelt list
