
open Prims
open FStar_Pervasives
type binding =
| Binding_var of FStar_Syntax_Syntax.bv
| Binding_lid of (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme)
| Binding_sig of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt)
| Binding_univ of FStar_Syntax_Syntax.univ_name
| Binding_sig_inst of (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes)


let uu___is_Binding_var : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
true
end
| uu____44 -> begin
false
end))


let __proj__Binding_var__item___0 : binding  ->  FStar_Syntax_Syntax.bv = (fun projectee -> (match (projectee) with
| Binding_var (_0) -> begin
_0
end))


let uu___is_Binding_lid : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
true
end
| uu____62 -> begin
false
end))


let __proj__Binding_lid__item___0 : binding  ->  (FStar_Ident.lident * FStar_Syntax_Syntax.tscheme) = (fun projectee -> (match (projectee) with
| Binding_lid (_0) -> begin
_0
end))


let uu___is_Binding_sig : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_sig (_0) -> begin
true
end
| uu____94 -> begin
false
end))


let __proj__Binding_sig__item___0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt) = (fun projectee -> (match (projectee) with
| Binding_sig (_0) -> begin
_0
end))


let uu___is_Binding_univ : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
true
end
| uu____126 -> begin
false
end))


let __proj__Binding_univ__item___0 : binding  ->  FStar_Syntax_Syntax.univ_name = (fun projectee -> (match (projectee) with
| Binding_univ (_0) -> begin
_0
end))


let uu___is_Binding_sig_inst : binding  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_0) -> begin
true
end
| uu____148 -> begin
false
end))


let __proj__Binding_sig_inst__item___0 : binding  ->  (FStar_Ident.lident Prims.list * FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes) = (fun projectee -> (match (projectee) with
| Binding_sig_inst (_0) -> begin
_0
end))

type delta_level =
| NoDelta
| Inlining
| Eager_unfolding_only
| Unfold of FStar_Syntax_Syntax.delta_depth
| UnfoldTac


let uu___is_NoDelta : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| NoDelta -> begin
true
end
| uu____189 -> begin
false
end))


let uu___is_Inlining : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Inlining -> begin
true
end
| uu____194 -> begin
false
end))


let uu___is_Eager_unfolding_only : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Eager_unfolding_only -> begin
true
end
| uu____199 -> begin
false
end))


let uu___is_Unfold : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
true
end
| uu____205 -> begin
false
end))


let __proj__Unfold__item___0 : delta_level  ->  FStar_Syntax_Syntax.delta_depth = (fun projectee -> (match (projectee) with
| Unfold (_0) -> begin
_0
end))


let uu___is_UnfoldTac : delta_level  ->  Prims.bool = (fun projectee -> (match (projectee) with
| UnfoldTac -> begin
true
end
| uu____218 -> begin
false
end))

type mlift =
{mlift_wp : FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ; mlift_term : (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option}


let __proj__Mkmlift__item__mlift_wp : mlift  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ = (fun projectee -> (match (projectee) with
| {mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term} -> begin
__fname__mlift_wp
end))


let __proj__Mkmlift__item__mlift_term : mlift  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {mlift_wp = __fname__mlift_wp; mlift_term = __fname__mlift_term} -> begin
__fname__mlift_term
end))

type edge =
{msource : FStar_Ident.lident; mtarget : FStar_Ident.lident; mlift : mlift}


let __proj__Mkedge__item__msource : edge  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mtarget = __fname__mtarget; mlift = __fname__mlift} -> begin
__fname__msource
end))


let __proj__Mkedge__item__mtarget : edge  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mtarget = __fname__mtarget; mlift = __fname__mlift} -> begin
__fname__mtarget
end))


let __proj__Mkedge__item__mlift : edge  ->  mlift = (fun projectee -> (match (projectee) with
| {msource = __fname__msource; mtarget = __fname__mtarget; mlift = __fname__mlift} -> begin
__fname__mlift
end))

type effects =
{decls : (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) Prims.list; order : edge Prims.list; joins : (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list}


let __proj__Mkeffects__item__decls : effects  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) Prims.list = (fun projectee -> (match (projectee) with
| {decls = __fname__decls; order = __fname__order; joins = __fname__joins} -> begin
__fname__decls
end))


let __proj__Mkeffects__item__order : effects  ->  edge Prims.list = (fun projectee -> (match (projectee) with
| {decls = __fname__decls; order = __fname__order; joins = __fname__joins} -> begin
__fname__order
end))


let __proj__Mkeffects__item__joins : effects  ->  (FStar_Ident.lident * FStar_Ident.lident * FStar_Ident.lident * mlift * mlift) Prims.list = (fun projectee -> (match (projectee) with
| {decls = __fname__decls; order = __fname__order; joins = __fname__joins} -> begin
__fname__joins
end))


type name_prefix =
Prims.string Prims.list


type flat_proof_namespace =
(name_prefix * Prims.bool) Prims.list


type proof_namespace =
flat_proof_namespace Prims.list


type cached_elt =
(((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)) FStar_Util.either * FStar_Range.range)


type goal =
FStar_Syntax_Syntax.term

type env =
{solver : solver_t; range : FStar_Range.range; curmodule : FStar_Ident.lident; gamma : binding Prims.list; gamma_cache : cached_elt FStar_Util.smap; modules : FStar_Syntax_Syntax.modul Prims.list; expected_typ : FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option; sigtab : FStar_Syntax_Syntax.sigelt FStar_Util.smap; is_pattern : Prims.bool; instantiate_imp : Prims.bool; effects : effects; generalize : Prims.bool; letrecs : (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list; top_level : Prims.bool; check_uvars : Prims.bool; use_eq : Prims.bool; is_iface : Prims.bool; admit : Prims.bool; lax : Prims.bool; lax_universes : Prims.bool; failhard : Prims.bool; nosynth : Prims.bool; tc_term : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t); type_of : env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t); universe_of : env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe; use_bv_sorts : Prims.bool; qname_and_index : (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option; proof_ns : proof_namespace; synth : env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term; is_native_tactic : FStar_Ident.lid  ->  Prims.bool; identifier_info : FStar_TypeChecker_Common.id_info_table FStar_ST.ref; tc_hooks : tcenv_hooks; dsenv : FStar_ToSyntax_Env.env} 
 and solver_t =
{init : env  ->  Prims.unit; push : Prims.string  ->  Prims.unit; pop : Prims.string  ->  Prims.unit; encode_modul : env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit; encode_sig : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit; preprocess : env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list; solve : (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit; finish : Prims.unit  ->  Prims.unit; refresh : Prims.unit  ->  Prims.unit} 
 and guard_t =
{guard_f : FStar_TypeChecker_Common.guard_formula; deferred : FStar_TypeChecker_Common.deferred; univ_ineqs : (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list); implicits : (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list} 
 and tcenv_hooks =
{tc_push_in_gamma_hook : env  ->  binding  ->  Prims.unit}


let __proj__Mkenv__item__solver : env  ->  solver_t = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__solver
end))


let __proj__Mkenv__item__range : env  ->  FStar_Range.range = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__range
end))


let __proj__Mkenv__item__curmodule : env  ->  FStar_Ident.lident = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__curmodule
end))


let __proj__Mkenv__item__gamma : env  ->  binding Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__gamma
end))


let __proj__Mkenv__item__gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__gamma_cache
end))


let __proj__Mkenv__item__modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__modules
end))


let __proj__Mkenv__item__expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__expected_typ
end))


let __proj__Mkenv__item__sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__sigtab
end))


let __proj__Mkenv__item__is_pattern : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__is_pattern
end))


let __proj__Mkenv__item__instantiate_imp : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__instantiate_imp
end))


let __proj__Mkenv__item__effects : env  ->  effects = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__effects
end))


let __proj__Mkenv__item__generalize : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__generalize
end))


let __proj__Mkenv__item__letrecs : env  ->  (FStar_Syntax_Syntax.lbname * FStar_Syntax_Syntax.typ) Prims.list = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__letrecs
end))


let __proj__Mkenv__item__top_level : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__top_level
end))


let __proj__Mkenv__item__check_uvars : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__check_uvars
end))


let __proj__Mkenv__item__use_eq : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__use_eq
end))


let __proj__Mkenv__item__is_iface : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__is_iface
end))


let __proj__Mkenv__item__admit : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__admit
end))


let __proj__Mkenv__item__lax : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__lax
end))


let __proj__Mkenv__item__lax_universes : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__lax_universes
end))


let __proj__Mkenv__item__failhard : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__failhard
end))


let __proj__Mkenv__item__nosynth : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__nosynth
end))


let __proj__Mkenv__item__tc_term : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t) = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__tc_term
end))


let __proj__Mkenv__item__type_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t) = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__type_of
end))


let __proj__Mkenv__item__universe_of : env  ->  env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__universe_of
end))


let __proj__Mkenv__item__use_bv_sorts : env  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__use_bv_sorts
end))


let __proj__Mkenv__item__qname_and_index : env  ->  (FStar_Ident.lident * Prims.int) FStar_Pervasives_Native.option = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__qname_and_index
end))


let __proj__Mkenv__item__proof_ns : env  ->  proof_namespace = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__proof_ns
end))


let __proj__Mkenv__item__synth : env  ->  env  ->  FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.term = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__synth
end))


let __proj__Mkenv__item__is_native_tactic : env  ->  FStar_Ident.lid  ->  Prims.bool = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__is_native_tactic
end))


let __proj__Mkenv__item__identifier_info : env  ->  FStar_TypeChecker_Common.id_info_table FStar_ST.ref = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__identifier_info
end))


let __proj__Mkenv__item__tc_hooks : env  ->  tcenv_hooks = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__tc_hooks
end))


let __proj__Mkenv__item__dsenv : env  ->  FStar_ToSyntax_Env.env = (fun projectee -> (match (projectee) with
| {solver = __fname__solver; range = __fname__range; curmodule = __fname__curmodule; gamma = __fname__gamma; gamma_cache = __fname__gamma_cache; modules = __fname__modules; expected_typ = __fname__expected_typ; sigtab = __fname__sigtab; is_pattern = __fname__is_pattern; instantiate_imp = __fname__instantiate_imp; effects = __fname__effects; generalize = __fname__generalize; letrecs = __fname__letrecs; top_level = __fname__top_level; check_uvars = __fname__check_uvars; use_eq = __fname__use_eq; is_iface = __fname__is_iface; admit = __fname__admit; lax = __fname__lax; lax_universes = __fname__lax_universes; failhard = __fname__failhard; nosynth = __fname__nosynth; tc_term = __fname__tc_term; type_of = __fname__type_of; universe_of = __fname__universe_of; use_bv_sorts = __fname__use_bv_sorts; qname_and_index = __fname__qname_and_index; proof_ns = __fname__proof_ns; synth = __fname__synth; is_native_tactic = __fname__is_native_tactic; identifier_info = __fname__identifier_info; tc_hooks = __fname__tc_hooks; dsenv = __fname__dsenv} -> begin
__fname__dsenv
end))


let __proj__Mksolver_t__item__init : solver_t  ->  env  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__init
end))


let __proj__Mksolver_t__item__push : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__push
end))


let __proj__Mksolver_t__item__pop : solver_t  ->  Prims.string  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__pop
end))


let __proj__Mksolver_t__item__encode_modul : solver_t  ->  env  ->  FStar_Syntax_Syntax.modul  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__encode_modul
end))


let __proj__Mksolver_t__item__encode_sig : solver_t  ->  env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__encode_sig
end))


let __proj__Mksolver_t__item__preprocess : solver_t  ->  env  ->  goal  ->  (env * goal * FStar_Options.optionstate) Prims.list = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__preprocess
end))


let __proj__Mksolver_t__item__solve : solver_t  ->  (Prims.unit  ->  Prims.string) FStar_Pervasives_Native.option  ->  env  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__solve
end))


let __proj__Mksolver_t__item__finish : solver_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__finish
end))


let __proj__Mksolver_t__item__refresh : solver_t  ->  Prims.unit  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {init = __fname__init; push = __fname__push; pop = __fname__pop; encode_modul = __fname__encode_modul; encode_sig = __fname__encode_sig; preprocess = __fname__preprocess; solve = __fname__solve; finish = __fname__finish; refresh = __fname__refresh} -> begin
__fname__refresh
end))


let __proj__Mkguard_t__item__guard_f : guard_t  ->  FStar_TypeChecker_Common.guard_formula = (fun projectee -> (match (projectee) with
| {guard_f = __fname__guard_f; deferred = __fname__deferred; univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits} -> begin
__fname__guard_f
end))


let __proj__Mkguard_t__item__deferred : guard_t  ->  FStar_TypeChecker_Common.deferred = (fun projectee -> (match (projectee) with
| {guard_f = __fname__guard_f; deferred = __fname__deferred; univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits} -> begin
__fname__deferred
end))


let __proj__Mkguard_t__item__univ_ineqs : guard_t  ->  (FStar_Syntax_Syntax.universe Prims.list * FStar_TypeChecker_Common.univ_ineq Prims.list) = (fun projectee -> (match (projectee) with
| {guard_f = __fname__guard_f; deferred = __fname__deferred; univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits} -> begin
__fname__univ_ineqs
end))


let __proj__Mkguard_t__item__implicits : guard_t  ->  (Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list = (fun projectee -> (match (projectee) with
| {guard_f = __fname__guard_f; deferred = __fname__deferred; univ_ineqs = __fname__univ_ineqs; implicits = __fname__implicits} -> begin
__fname__implicits
end))


let __proj__Mktcenv_hooks__item__tc_push_in_gamma_hook : tcenv_hooks  ->  env  ->  binding  ->  Prims.unit = (fun projectee -> (match (projectee) with
| {tc_push_in_gamma_hook = __fname__tc_push_in_gamma_hook} -> begin
__fname__tc_push_in_gamma_hook
end))


type implicits =
(Prims.string * env * FStar_Syntax_Syntax.uvar * FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * FStar_Range.range) Prims.list


let default_tc_hooks : tcenv_hooks = {tc_push_in_gamma_hook = (fun uu____4910 uu____4911 -> ())}


let tc_hooks : env  ->  tcenv_hooks = (fun env -> env.tc_hooks)


let set_tc_hooks : env  ->  tcenv_hooks  ->  env = (fun env hooks -> (

let uu___143_4924 = env
in {solver = uu___143_4924.solver; range = uu___143_4924.range; curmodule = uu___143_4924.curmodule; gamma = uu___143_4924.gamma; gamma_cache = uu___143_4924.gamma_cache; modules = uu___143_4924.modules; expected_typ = uu___143_4924.expected_typ; sigtab = uu___143_4924.sigtab; is_pattern = uu___143_4924.is_pattern; instantiate_imp = uu___143_4924.instantiate_imp; effects = uu___143_4924.effects; generalize = uu___143_4924.generalize; letrecs = uu___143_4924.letrecs; top_level = uu___143_4924.top_level; check_uvars = uu___143_4924.check_uvars; use_eq = uu___143_4924.use_eq; is_iface = uu___143_4924.is_iface; admit = uu___143_4924.admit; lax = uu___143_4924.lax; lax_universes = uu___143_4924.lax_universes; failhard = uu___143_4924.failhard; nosynth = uu___143_4924.nosynth; tc_term = uu___143_4924.tc_term; type_of = uu___143_4924.type_of; universe_of = uu___143_4924.universe_of; use_bv_sorts = uu___143_4924.use_bv_sorts; qname_and_index = uu___143_4924.qname_and_index; proof_ns = uu___143_4924.proof_ns; synth = uu___143_4924.synth; is_native_tactic = uu___143_4924.is_native_tactic; identifier_info = uu___143_4924.identifier_info; tc_hooks = hooks; dsenv = uu___143_4924.dsenv}))


type env_t =
env


type sigtable =
FStar_Syntax_Syntax.sigelt FStar_Util.smap


let should_verify : env  ->  Prims.bool = (fun env -> (((not (env.lax)) && (not (env.admit))) && (FStar_Options.should_verify env.curmodule.FStar_Ident.str)))


let visible_at : delta_level  ->  FStar_Syntax_Syntax.qualifier  ->  Prims.bool = (fun d q -> (match (((d), (q))) with
| (NoDelta, uu____4939) -> begin
true
end
| (Eager_unfolding_only, FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____4940), FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen) -> begin
true
end
| (Unfold (uu____4941), FStar_Syntax_Syntax.Visible_default) -> begin
true
end
| (Inlining, FStar_Syntax_Syntax.Inline_for_extraction) -> begin
true
end
| uu____4942 -> begin
false
end))


let default_table_size : Prims.int = (Prims.parse_int "200")


let new_sigtab : 'Auu____4951 . Prims.unit  ->  'Auu____4951 FStar_Util.smap = (fun uu____4957 -> (FStar_Util.smap_create default_table_size))


let new_gamma_cache : 'Auu____4962 . Prims.unit  ->  'Auu____4962 FStar_Util.smap = (fun uu____4968 -> (FStar_Util.smap_create (Prims.parse_int "100")))


let initial_env : (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.lcomp * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  (FStar_Syntax_Syntax.term * FStar_Syntax_Syntax.typ * guard_t))  ->  (env  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.universe)  ->  solver_t  ->  FStar_Ident.lident  ->  env = (fun tc_term type_of universe_of solver module_lid -> (

let uu____5043 = (new_gamma_cache ())
in (

let uu____5046 = (new_sigtab ())
in (

let uu____5049 = (

let uu____5050 = (FStar_Options.using_facts_from ())
in (match (uu____5050) with
| FStar_Pervasives_Native.Some (ns) -> begin
(

let uu____5060 = (

let uu____5069 = (FStar_List.map (fun s -> (((FStar_Ident.path_of_text s)), (true))) ns)
in (FStar_List.append uu____5069 (((([]), (false)))::[])))
in (uu____5060)::[])
end
| FStar_Pervasives_Native.None -> begin
([])::[]
end))
in (

let uu____5142 = (FStar_Util.mk_ref FStar_TypeChecker_Common.id_info_table_empty)
in (

let uu____5145 = (FStar_ToSyntax_Env.empty_env ())
in {solver = solver; range = FStar_Range.dummyRange; curmodule = module_lid; gamma = []; gamma_cache = uu____5043; modules = []; expected_typ = FStar_Pervasives_Native.None; sigtab = uu____5046; is_pattern = false; instantiate_imp = true; effects = {decls = []; order = []; joins = []}; generalize = true; letrecs = []; top_level = false; check_uvars = false; use_eq = false; is_iface = false; admit = false; lax = false; lax_universes = false; failhard = false; nosynth = false; tc_term = tc_term; type_of = type_of; universe_of = universe_of; use_bv_sorts = false; qname_and_index = FStar_Pervasives_Native.None; proof_ns = uu____5049; synth = (fun e g tau -> (failwith "no synthesizer available")); is_native_tactic = (fun uu____5177 -> false); identifier_info = uu____5142; tc_hooks = default_tc_hooks; dsenv = uu____5145}))))))


let sigtab : env  ->  FStar_Syntax_Syntax.sigelt FStar_Util.smap = (fun env -> env.sigtab)


let gamma_cache : env  ->  cached_elt FStar_Util.smap = (fun env -> env.gamma_cache)


let query_indices : (FStar_Ident.lident * Prims.int) Prims.list Prims.list FStar_ST.ref = (FStar_Util.mk_ref (([])::[]))


let push_query_indices : Prims.unit  ->  Prims.unit = (fun uu____5248 -> (

let uu____5249 = (FStar_ST.op_Bang query_indices)
in (match (uu____5249) with
| [] -> begin
(failwith "Empty query indices!")
end
| uu____5326 -> begin
(

let uu____5335 = (

let uu____5344 = (

let uu____5351 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____5351))
in (

let uu____5428 = (FStar_ST.op_Bang query_indices)
in (uu____5344)::uu____5428))
in (FStar_ST.op_Colon_Equals query_indices uu____5335))
end)))


let pop_query_indices : Prims.unit  ->  Prims.unit = (fun uu____5570 -> (

let uu____5571 = (FStar_ST.op_Bang query_indices)
in (match (uu____5571) with
| [] -> begin
(failwith "Empty query indices!")
end
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices tl1)
end)))


let add_query_index : (FStar_Ident.lident * Prims.int)  ->  Prims.unit = (fun uu____5739 -> (match (uu____5739) with
| (l, n1) -> begin
(

let uu____5746 = (FStar_ST.op_Bang query_indices)
in (match (uu____5746) with
| (hd1)::tl1 -> begin
(FStar_ST.op_Colon_Equals query_indices (((((l), (n1)))::hd1)::tl1))
end
| uu____5911 -> begin
(failwith "Empty query indices")
end))
end))


let peek_query_indices : Prims.unit  ->  (FStar_Ident.lident * Prims.int) Prims.list = (fun uu____5929 -> (

let uu____5930 = (FStar_ST.op_Bang query_indices)
in (FStar_List.hd uu____5930)))


let stack : env Prims.list FStar_ST.ref = (FStar_Util.mk_ref [])


let push_stack : env  ->  env = (fun env -> ((

let uu____6025 = (

let uu____6028 = (FStar_ST.op_Bang stack)
in (env)::uu____6028)
in (FStar_ST.op_Colon_Equals stack uu____6025));
(

let uu___144_6131 = env
in (

let uu____6132 = (FStar_Util.smap_copy (gamma_cache env))
in (

let uu____6135 = (FStar_Util.smap_copy (sigtab env))
in (

let uu____6138 = (

let uu____6141 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_Util.mk_ref uu____6141))
in {solver = uu___144_6131.solver; range = uu___144_6131.range; curmodule = uu___144_6131.curmodule; gamma = uu___144_6131.gamma; gamma_cache = uu____6132; modules = uu___144_6131.modules; expected_typ = uu___144_6131.expected_typ; sigtab = uu____6135; is_pattern = uu___144_6131.is_pattern; instantiate_imp = uu___144_6131.instantiate_imp; effects = uu___144_6131.effects; generalize = uu___144_6131.generalize; letrecs = uu___144_6131.letrecs; top_level = uu___144_6131.top_level; check_uvars = uu___144_6131.check_uvars; use_eq = uu___144_6131.use_eq; is_iface = uu___144_6131.is_iface; admit = uu___144_6131.admit; lax = uu___144_6131.lax; lax_universes = uu___144_6131.lax_universes; failhard = uu___144_6131.failhard; nosynth = uu___144_6131.nosynth; tc_term = uu___144_6131.tc_term; type_of = uu___144_6131.type_of; universe_of = uu___144_6131.universe_of; use_bv_sorts = uu___144_6131.use_bv_sorts; qname_and_index = uu___144_6131.qname_and_index; proof_ns = uu___144_6131.proof_ns; synth = uu___144_6131.synth; is_native_tactic = uu___144_6131.is_native_tactic; identifier_info = uu____6138; tc_hooks = uu___144_6131.tc_hooks; dsenv = uu___144_6131.dsenv}))));
))


let pop_stack : Prims.unit  ->  env = (fun uu____6205 -> (

let uu____6206 = (FStar_ST.op_Bang stack)
in (match (uu____6206) with
| (env)::tl1 -> begin
((FStar_ST.op_Colon_Equals stack tl1);
env;
)
end
| uu____6314 -> begin
(failwith "Impossible: Too many pops")
end)))


let push : env  ->  Prims.string  ->  env = (fun env msg -> ((push_query_indices ());
(env.solver.push msg);
(push_stack env);
))


let pop : env  ->  Prims.string  ->  env = (fun env msg -> ((env.solver.pop msg);
(pop_query_indices ());
(pop_stack ());
))


let incr_query_index : env  ->  env = (fun env -> (

let qix = (peek_query_indices ())
in (match (env.qname_and_index) with
| FStar_Pervasives_Native.None -> begin
env
end
| FStar_Pervasives_Native.Some (l, n1) -> begin
(

let uu____6358 = (FStar_All.pipe_right qix (FStar_List.tryFind (fun uu____6384 -> (match (uu____6384) with
| (m, uu____6390) -> begin
(FStar_Ident.lid_equals l m)
end))))
in (match (uu____6358) with
| FStar_Pervasives_Native.None -> begin
(

let next = (n1 + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___145_6397 = env
in {solver = uu___145_6397.solver; range = uu___145_6397.range; curmodule = uu___145_6397.curmodule; gamma = uu___145_6397.gamma; gamma_cache = uu___145_6397.gamma_cache; modules = uu___145_6397.modules; expected_typ = uu___145_6397.expected_typ; sigtab = uu___145_6397.sigtab; is_pattern = uu___145_6397.is_pattern; instantiate_imp = uu___145_6397.instantiate_imp; effects = uu___145_6397.effects; generalize = uu___145_6397.generalize; letrecs = uu___145_6397.letrecs; top_level = uu___145_6397.top_level; check_uvars = uu___145_6397.check_uvars; use_eq = uu___145_6397.use_eq; is_iface = uu___145_6397.is_iface; admit = uu___145_6397.admit; lax = uu___145_6397.lax; lax_universes = uu___145_6397.lax_universes; failhard = uu___145_6397.failhard; nosynth = uu___145_6397.nosynth; tc_term = uu___145_6397.tc_term; type_of = uu___145_6397.type_of; universe_of = uu___145_6397.universe_of; use_bv_sorts = uu___145_6397.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___145_6397.proof_ns; synth = uu___145_6397.synth; is_native_tactic = uu___145_6397.is_native_tactic; identifier_info = uu___145_6397.identifier_info; tc_hooks = uu___145_6397.tc_hooks; dsenv = uu___145_6397.dsenv});
))
end
| FStar_Pervasives_Native.Some (uu____6402, m) -> begin
(

let next = (m + (Prims.parse_int "1"))
in ((add_query_index ((l), (next)));
(

let uu___146_6410 = env
in {solver = uu___146_6410.solver; range = uu___146_6410.range; curmodule = uu___146_6410.curmodule; gamma = uu___146_6410.gamma; gamma_cache = uu___146_6410.gamma_cache; modules = uu___146_6410.modules; expected_typ = uu___146_6410.expected_typ; sigtab = uu___146_6410.sigtab; is_pattern = uu___146_6410.is_pattern; instantiate_imp = uu___146_6410.instantiate_imp; effects = uu___146_6410.effects; generalize = uu___146_6410.generalize; letrecs = uu___146_6410.letrecs; top_level = uu___146_6410.top_level; check_uvars = uu___146_6410.check_uvars; use_eq = uu___146_6410.use_eq; is_iface = uu___146_6410.is_iface; admit = uu___146_6410.admit; lax = uu___146_6410.lax; lax_universes = uu___146_6410.lax_universes; failhard = uu___146_6410.failhard; nosynth = uu___146_6410.nosynth; tc_term = uu___146_6410.tc_term; type_of = uu___146_6410.type_of; universe_of = uu___146_6410.universe_of; use_bv_sorts = uu___146_6410.use_bv_sorts; qname_and_index = FStar_Pervasives_Native.Some (((l), (next))); proof_ns = uu___146_6410.proof_ns; synth = uu___146_6410.synth; is_native_tactic = uu___146_6410.is_native_tactic; identifier_info = uu___146_6410.identifier_info; tc_hooks = uu___146_6410.tc_hooks; dsenv = uu___146_6410.dsenv});
))
end))
end)))


let debug : env  ->  FStar_Options.debug_level_t  ->  Prims.bool = (fun env l -> (FStar_Options.debug_at_level env.curmodule.FStar_Ident.str l))


let set_range : env  ->  FStar_Range.range  ->  env = (fun e r -> (match ((Prims.op_Equality r FStar_Range.dummyRange)) with
| true -> begin
e
end
| uu____6431 -> begin
(

let uu___147_6432 = e
in {solver = uu___147_6432.solver; range = r; curmodule = uu___147_6432.curmodule; gamma = uu___147_6432.gamma; gamma_cache = uu___147_6432.gamma_cache; modules = uu___147_6432.modules; expected_typ = uu___147_6432.expected_typ; sigtab = uu___147_6432.sigtab; is_pattern = uu___147_6432.is_pattern; instantiate_imp = uu___147_6432.instantiate_imp; effects = uu___147_6432.effects; generalize = uu___147_6432.generalize; letrecs = uu___147_6432.letrecs; top_level = uu___147_6432.top_level; check_uvars = uu___147_6432.check_uvars; use_eq = uu___147_6432.use_eq; is_iface = uu___147_6432.is_iface; admit = uu___147_6432.admit; lax = uu___147_6432.lax; lax_universes = uu___147_6432.lax_universes; failhard = uu___147_6432.failhard; nosynth = uu___147_6432.nosynth; tc_term = uu___147_6432.tc_term; type_of = uu___147_6432.type_of; universe_of = uu___147_6432.universe_of; use_bv_sorts = uu___147_6432.use_bv_sorts; qname_and_index = uu___147_6432.qname_and_index; proof_ns = uu___147_6432.proof_ns; synth = uu___147_6432.synth; is_native_tactic = uu___147_6432.is_native_tactic; identifier_info = uu___147_6432.identifier_info; tc_hooks = uu___147_6432.tc_hooks; dsenv = uu___147_6432.dsenv})
end))


let get_range : env  ->  FStar_Range.range = (fun e -> e.range)


let toggle_id_info : env  ->  Prims.bool  ->  Prims.unit = (fun env enabled -> (

let uu____6445 = (

let uu____6446 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_toggle uu____6446 enabled))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____6445)))


let insert_bv_info : env  ->  FStar_Syntax_Syntax.bv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env bv ty -> (

let uu____6551 = (

let uu____6552 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_bv uu____6552 bv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____6551)))


let insert_fv_info : env  ->  FStar_Syntax_Syntax.fv  ->  FStar_Syntax_Syntax.typ  ->  Prims.unit = (fun env fv ty -> (

let uu____6657 = (

let uu____6658 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_insert_fv uu____6658 fv ty))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____6657)))


let promote_id_info : env  ->  (FStar_Syntax_Syntax.typ  ->  FStar_Syntax_Syntax.typ)  ->  Prims.unit = (fun env ty_map -> (

let uu____6764 = (

let uu____6765 = (FStar_ST.op_Bang env.identifier_info)
in (FStar_TypeChecker_Common.id_info_promote uu____6765 ty_map))
in (FStar_ST.op_Colon_Equals env.identifier_info uu____6764)))


let modules : env  ->  FStar_Syntax_Syntax.modul Prims.list = (fun env -> env.modules)


let current_module : env  ->  FStar_Ident.lident = (fun env -> env.curmodule)


let set_current_module : env  ->  FStar_Ident.lident  ->  env = (fun env lid -> (

let uu___148_6876 = env
in {solver = uu___148_6876.solver; range = uu___148_6876.range; curmodule = lid; gamma = uu___148_6876.gamma; gamma_cache = uu___148_6876.gamma_cache; modules = uu___148_6876.modules; expected_typ = uu___148_6876.expected_typ; sigtab = uu___148_6876.sigtab; is_pattern = uu___148_6876.is_pattern; instantiate_imp = uu___148_6876.instantiate_imp; effects = uu___148_6876.effects; generalize = uu___148_6876.generalize; letrecs = uu___148_6876.letrecs; top_level = uu___148_6876.top_level; check_uvars = uu___148_6876.check_uvars; use_eq = uu___148_6876.use_eq; is_iface = uu___148_6876.is_iface; admit = uu___148_6876.admit; lax = uu___148_6876.lax; lax_universes = uu___148_6876.lax_universes; failhard = uu___148_6876.failhard; nosynth = uu___148_6876.nosynth; tc_term = uu___148_6876.tc_term; type_of = uu___148_6876.type_of; universe_of = uu___148_6876.universe_of; use_bv_sorts = uu___148_6876.use_bv_sorts; qname_and_index = uu___148_6876.qname_and_index; proof_ns = uu___148_6876.proof_ns; synth = uu___148_6876.synth; is_native_tactic = uu___148_6876.is_native_tactic; identifier_info = uu___148_6876.identifier_info; tc_hooks = uu___148_6876.tc_hooks; dsenv = uu___148_6876.dsenv}))


let has_interface : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (FStar_All.pipe_right env.modules (FStar_Util.for_some (fun m -> (m.FStar_Syntax_Syntax.is_interface && (FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name l))))))


let find_in_sigtab : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.sigelt FStar_Pervasives_Native.option = (fun env lid -> (FStar_Util.smap_try_find (sigtab env) (FStar_Ident.text_of_lid lid)))


let name_not_found : FStar_Ident.lid  ->  Prims.string = (fun l -> (FStar_Util.format1 "Name \"%s\" not found" l.FStar_Ident.str))


let variable_not_found : FStar_Syntax_Syntax.bv  ->  Prims.string = (fun v1 -> (

let uu____6907 = (FStar_Syntax_Print.bv_to_string v1)
in (FStar_Util.format1 "Variable \"%s\" not found" uu____6907)))


let new_u_univ : Prims.unit  ->  FStar_Syntax_Syntax.universe = (fun uu____6911 -> (

let uu____6912 = (FStar_Syntax_Unionfind.univ_fresh ())
in FStar_Syntax_Syntax.U_unif (uu____6912)))


let inst_tscheme_with : FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.universes  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun ts us -> (match (((ts), (us))) with
| (([], t), []) -> begin
(([]), (t))
end
| ((formals, t), uu____6952) -> begin
(

let n1 = ((FStar_List.length formals) - (Prims.parse_int "1"))
in (

let vs = (FStar_All.pipe_right us (FStar_List.mapi (fun i u -> FStar_Syntax_Syntax.UN ((((n1 - i)), (u))))))
in (

let uu____6976 = (FStar_Syntax_Subst.subst vs t)
in ((us), (uu____6976)))))
end))


let inst_tscheme : FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun uu___130_6990 -> (match (uu___130_6990) with
| ([], t) -> begin
(([]), (t))
end
| (us, t) -> begin
(

let us' = (FStar_All.pipe_right us (FStar_List.map (fun uu____7014 -> (new_u_univ ()))))
in (inst_tscheme_with ((us), (t)) us'))
end))


let inst_tscheme_with_range : FStar_Range.range  ->  FStar_Syntax_Syntax.tscheme  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) = (fun r t -> (

let uu____7029 = (inst_tscheme t)
in (match (uu____7029) with
| (us, t1) -> begin
(

let uu____7040 = (FStar_Syntax_Subst.set_use_range r t1)
in ((us), (uu____7040)))
end)))


let inst_effect_fun_with : FStar_Syntax_Syntax.universes  ->  env  ->  FStar_Syntax_Syntax.eff_decl  ->  FStar_Syntax_Syntax.tscheme  ->  FStar_Syntax_Syntax.term = (fun insts env ed uu____7056 -> (match (uu____7056) with
| (us, t) -> begin
(match (ed.FStar_Syntax_Syntax.binders) with
| [] -> begin
(

let univs1 = (FStar_List.append ed.FStar_Syntax_Syntax.univs us)
in ((match ((Prims.op_disEquality (FStar_List.length insts) (FStar_List.length univs1))) with
| true -> begin
(

let uu____7071 = (

let uu____7072 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (

let uu____7073 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length insts))
in (

let uu____7074 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (

let uu____7075 = (FStar_Syntax_Print.term_to_string t)
in (FStar_Util.format4 "Expected %s instantiations; got %s; failed universe instantiation in effect %s\n\t%s\n" uu____7072 uu____7073 uu____7074 uu____7075)))))
in (failwith uu____7071))
end
| uu____7076 -> begin
()
end);
(

let uu____7077 = (inst_tscheme_with (((FStar_List.append ed.FStar_Syntax_Syntax.univs us)), (t)) insts)
in (FStar_Pervasives_Native.snd uu____7077));
))
end
| uu____7084 -> begin
(

let uu____7085 = (

let uu____7086 = (FStar_Syntax_Print.lid_to_string ed.FStar_Syntax_Syntax.mname)
in (FStar_Util.format1 "Unexpected use of an uninstantiated effect: %s\n" uu____7086))
in (failwith uu____7085))
end)
end))

type tri =
| Yes
| No
| Maybe


let uu___is_Yes : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Yes -> begin
true
end
| uu____7091 -> begin
false
end))


let uu___is_No : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| No -> begin
true
end
| uu____7096 -> begin
false
end))


let uu___is_Maybe : tri  ->  Prims.bool = (fun projectee -> (match (projectee) with
| Maybe -> begin
true
end
| uu____7101 -> begin
false
end))


let in_cur_mod : env  ->  FStar_Ident.lident  ->  tri = (fun env l -> (

let cur = (current_module env)
in (match ((Prims.op_Equality l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
Yes
end
| uu____7111 -> begin
(match ((FStar_Util.starts_with l.FStar_Ident.nsstr cur.FStar_Ident.str)) with
| true -> begin
(

let lns = (FStar_List.append l.FStar_Ident.ns ((l.FStar_Ident.ident)::[]))
in (

let cur1 = (FStar_List.append cur.FStar_Ident.ns ((cur.FStar_Ident.ident)::[]))
in (

let rec aux = (fun c l1 -> (match (((c), (l1))) with
| ([], uu____7137) -> begin
Maybe
end
| (uu____7144, []) -> begin
No
end
| ((hd1)::tl1, (hd')::tl') when (Prims.op_Equality hd1.FStar_Ident.idText hd'.FStar_Ident.idText) -> begin
(aux tl1 tl')
end
| uu____7163 -> begin
No
end))
in (aux cur1 lns))))
end
| uu____7172 -> begin
No
end)
end)))


let lookup_qname : env  ->  FStar_Ident.lident  ->  (((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ), (FStar_Syntax_Syntax.sigelt * FStar_Syntax_Syntax.universes FStar_Pervasives_Native.option)) FStar_Util.either * FStar_Range.range) FStar_Pervasives_Native.option = (fun env lid -> (

let cur_mod = (in_cur_mod env lid)
in (

let cache = (fun t -> ((FStar_Util.smap_add (gamma_cache env) lid.FStar_Ident.str t);
FStar_Pervasives_Native.Some (t);
))
in (

let found = (match ((Prims.op_disEquality cur_mod No)) with
| true -> begin
(

let uu____7270 = (FStar_Util.smap_try_find (gamma_cache env) lid.FStar_Ident.str)
in (match (uu____7270) with
| FStar_Pervasives_Native.None -> begin
(FStar_Util.find_map env.gamma (fun uu___131_7315 -> (match (uu___131_7315) with
| Binding_lid (l, t) -> begin
(match ((FStar_Ident.lid_equals lid l)) with
| true -> begin
(

let uu____7358 = (

let uu____7377 = (

let uu____7392 = (inst_tscheme t)
in FStar_Util.Inl (uu____7392))
in ((uu____7377), ((FStar_Ident.range_of_lid l))))
in FStar_Pervasives_Native.Some (uu____7358))
end
| uu____7439 -> begin
FStar_Pervasives_Native.None
end)
end
| Binding_sig (uu____7458, {FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_bundle (ses, uu____7460); FStar_Syntax_Syntax.sigrng = uu____7461; FStar_Syntax_Syntax.sigquals = uu____7462; FStar_Syntax_Syntax.sigmeta = uu____7463; FStar_Syntax_Syntax.sigattrs = uu____7464}) -> begin
(FStar_Util.find_map ses (fun se -> (

let uu____7484 = (FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se) (FStar_Util.for_some (FStar_Ident.lid_equals lid)))
in (match (uu____7484) with
| true -> begin
(cache ((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| uu____7515 -> begin
FStar_Pervasives_Native.None
end))))
end
| Binding_sig (lids, s) -> begin
(

let maybe_cache = (fun t -> (match (s.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____7530) -> begin
FStar_Pervasives_Native.Some (t)
end
| uu____7537 -> begin
(cache t)
end))
in (

let uu____7538 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____7538) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
(maybe_cache ((FStar_Util.Inr (((s), (FStar_Pervasives_Native.None)))), ((FStar_Ident.range_of_lid l))))
end)))
end
| Binding_sig_inst (lids, s, us) -> begin
(

let uu____7613 = (FStar_List.tryFind (FStar_Ident.lid_equals lid) lids)
in (match (uu____7613) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (l) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((s), (FStar_Pervasives_Native.Some (us))))), ((FStar_Ident.range_of_lid l))))
end))
end
| uu____7699 -> begin
FStar_Pervasives_Native.None
end)))
end
| se -> begin
se
end))
end
| uu____7721 -> begin
FStar_Pervasives_Native.None
end)
in (match ((FStar_Util.is_some found)) with
| true -> begin
found
end
| uu____7778 -> begin
(

let uu____7779 = (find_in_sigtab env lid)
in (match (uu____7779) with
| FStar_Pervasives_Native.Some (se) -> begin
FStar_Pervasives_Native.Some (((FStar_Util.Inr (((se), (FStar_Pervasives_Native.None)))), ((FStar_Syntax_Util.range_of_sigelt se))))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))
end)))))


let rec add_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  Prims.unit = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_bundle (ses, uu____7878) -> begin
(add_sigelts env ses)
end
| uu____7887 -> begin
(

let lids = (FStar_Syntax_Util.lids_of_sigelt se)
in ((FStar_List.iter (fun l -> (FStar_Util.smap_add (sigtab env) l.FStar_Ident.str se)) lids);
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(FStar_All.pipe_right ne.FStar_Syntax_Syntax.actions (FStar_List.iter (fun a -> (

let se_let = (FStar_Syntax_Util.action_as_lb ne.FStar_Syntax_Syntax.mname a)
in (FStar_Util.smap_add (sigtab env) a.FStar_Syntax_Syntax.action_name.FStar_Ident.str se_let)))))
end
| uu____7901 -> begin
()
end);
))
end))
and add_sigelts : env  ->  FStar_Syntax_Syntax.sigelt Prims.list  ->  Prims.unit = (fun env ses -> (FStar_All.pipe_right ses (FStar_List.iter (add_sigelt env))))


let try_lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) FStar_Pervasives_Native.option = (fun env bv -> (FStar_Util.find_map env.gamma (fun uu___132_7930 -> (match (uu___132_7930) with
| Binding_var (id) when (FStar_Syntax_Syntax.bv_eq id bv) -> begin
FStar_Pervasives_Native.Some (((id.FStar_Syntax_Syntax.sort), (id.FStar_Syntax_Syntax.ppname.FStar_Ident.idRange)))
end
| uu____7948 -> begin
FStar_Pervasives_Native.None
end))))


let lookup_type_of_let : FStar_Syntax_Syntax.sigelt  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se lid -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____7983, (lb)::[]), uu____7985) -> begin
(

let uu____7998 = (

let uu____8007 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____8016 = (FStar_Syntax_Syntax.range_of_lbname lb.FStar_Syntax_Syntax.lbname)
in ((uu____8007), (uu____8016))))
in FStar_Pervasives_Native.Some (uu____7998))
end
| FStar_Syntax_Syntax.Sig_let ((uu____8029, lbs), uu____8031) -> begin
(FStar_Util.find_map lbs (fun lb -> (match (lb.FStar_Syntax_Syntax.lbname) with
| FStar_Util.Inl (uu____8067) -> begin
(failwith "impossible")
end
| FStar_Util.Inr (fv) -> begin
(

let uu____8079 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____8079) with
| true -> begin
(

let uu____8090 = (

let uu____8099 = (inst_tscheme ((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbtyp)))
in (

let uu____8108 = (FStar_Syntax_Syntax.range_of_fv fv)
in ((uu____8099), (uu____8108))))
in FStar_Pervasives_Native.Some (uu____8090))
end
| uu____8121 -> begin
FStar_Pervasives_Native.None
end))
end)))
end
| uu____8130 -> begin
FStar_Pervasives_Native.None
end))


let effect_signature : FStar_Syntax_Syntax.sigelt  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term) * FStar_Range.range) FStar_Pervasives_Native.option = (fun se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let uu____8164 = (

let uu____8173 = (

let uu____8178 = (

let uu____8179 = (

let uu____8182 = (FStar_Syntax_Syntax.mk_Total ne.FStar_Syntax_Syntax.signature)
in (FStar_Syntax_Util.arrow ne.FStar_Syntax_Syntax.binders uu____8182))
in ((ne.FStar_Syntax_Syntax.univs), (uu____8179)))
in (inst_tscheme uu____8178))
in ((uu____8173), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____8164))
end
| FStar_Syntax_Syntax.Sig_effect_abbrev (lid, us, binders, uu____8202, uu____8203) -> begin
(

let uu____8208 = (

let uu____8217 = (

let uu____8222 = (

let uu____8223 = (

let uu____8226 = (FStar_Syntax_Syntax.mk_Total FStar_Syntax_Syntax.teff)
in (FStar_Syntax_Util.arrow binders uu____8226))
in ((us), (uu____8223)))
in (inst_tscheme uu____8222))
in ((uu____8217), (se.FStar_Syntax_Syntax.sigrng)))
in FStar_Pervasives_Native.Some (uu____8208))
end
| uu____8243 -> begin
FStar_Pervasives_Native.None
end))


let try_lookup_lid_aux : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env lid -> (

let mapper = (fun uu____8303 -> (match (uu____8303) with
| (lr, rng) -> begin
(match (lr) with
| FStar_Util.Inl (t) -> begin
FStar_Pervasives_Native.Some (((t), (rng)))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____8399, uvs, t, uu____8402, uu____8403, uu____8404); FStar_Syntax_Syntax.sigrng = uu____8405; FStar_Syntax_Syntax.sigquals = uu____8406; FStar_Syntax_Syntax.sigmeta = uu____8407; FStar_Syntax_Syntax.sigattrs = uu____8408}, FStar_Pervasives_Native.None) -> begin
(

let uu____8429 = (

let uu____8438 = (inst_tscheme ((uvs), (t)))
in ((uu____8438), (rng)))
in FStar_Pervasives_Native.Some (uu____8429))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (l, uvs, t); FStar_Syntax_Syntax.sigrng = uu____8458; FStar_Syntax_Syntax.sigquals = qs; FStar_Syntax_Syntax.sigmeta = uu____8460; FStar_Syntax_Syntax.sigattrs = uu____8461}, FStar_Pervasives_Native.None) -> begin
(

let uu____8478 = (

let uu____8479 = (in_cur_mod env l)
in (Prims.op_Equality uu____8479 Yes))
in (match (uu____8478) with
| true -> begin
(

let uu____8490 = ((FStar_All.pipe_right qs (FStar_List.contains FStar_Syntax_Syntax.Assumption)) || env.is_iface)
in (match (uu____8490) with
| true -> begin
(

let uu____8503 = (

let uu____8512 = (inst_tscheme ((uvs), (t)))
in ((uu____8512), (rng)))
in FStar_Pervasives_Native.Some (uu____8503))
end
| uu____8529 -> begin
FStar_Pervasives_Native.None
end))
end
| uu____8538 -> begin
(

let uu____8539 = (

let uu____8548 = (inst_tscheme ((uvs), (t)))
in ((uu____8548), (rng)))
in FStar_Pervasives_Native.Some (uu____8539))
end))
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____8569, uu____8570); FStar_Syntax_Syntax.sigrng = uu____8571; FStar_Syntax_Syntax.sigquals = uu____8572; FStar_Syntax_Syntax.sigmeta = uu____8573; FStar_Syntax_Syntax.sigattrs = uu____8574}, FStar_Pervasives_Native.None) -> begin
(match (tps) with
| [] -> begin
(

let uu____8613 = (

let uu____8622 = (inst_tscheme ((uvs), (k)))
in ((uu____8622), (rng)))
in FStar_Pervasives_Native.Some (uu____8613))
end
| uu____8639 -> begin
(

let uu____8640 = (

let uu____8649 = (

let uu____8654 = (

let uu____8655 = (

let uu____8658 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____8658))
in ((uvs), (uu____8655)))
in (inst_tscheme uu____8654))
in ((uu____8649), (rng)))
in FStar_Pervasives_Native.Some (uu____8640))
end)
end
| FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (lid1, uvs, tps, k, uu____8679, uu____8680); FStar_Syntax_Syntax.sigrng = uu____8681; FStar_Syntax_Syntax.sigquals = uu____8682; FStar_Syntax_Syntax.sigmeta = uu____8683; FStar_Syntax_Syntax.sigattrs = uu____8684}, FStar_Pervasives_Native.Some (us)) -> begin
(match (tps) with
| [] -> begin
(

let uu____8724 = (

let uu____8733 = (inst_tscheme_with ((uvs), (k)) us)
in ((uu____8733), (rng)))
in FStar_Pervasives_Native.Some (uu____8724))
end
| uu____8750 -> begin
(

let uu____8751 = (

let uu____8760 = (

let uu____8765 = (

let uu____8766 = (

let uu____8769 = (FStar_Syntax_Syntax.mk_Total k)
in (FStar_Syntax_Util.flat_arrow tps uu____8769))
in ((uvs), (uu____8766)))
in (inst_tscheme_with uu____8765 us))
in ((uu____8760), (rng)))
in FStar_Pervasives_Native.Some (uu____8751))
end)
end
| FStar_Util.Inr (se) -> begin
(

let uu____8803 = (match (se) with
| ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____8824); FStar_Syntax_Syntax.sigrng = uu____8825; FStar_Syntax_Syntax.sigquals = uu____8826; FStar_Syntax_Syntax.sigmeta = uu____8827; FStar_Syntax_Syntax.sigattrs = uu____8828}, FStar_Pervasives_Native.None) -> begin
(lookup_type_of_let (FStar_Pervasives_Native.fst se) lid)
end
| uu____8843 -> begin
(effect_signature (FStar_Pervasives_Native.fst se))
end)
in (FStar_All.pipe_right uu____8803 (FStar_Util.map_option (fun uu____8891 -> (match (uu____8891) with
| (us_t, rng1) -> begin
((us_t), (rng1))
end)))))
end)
end))
in (

let uu____8922 = (

let uu____8933 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____8933 mapper))
in (match (uu____8922) with
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
FStar_Pervasives_Native.Some (((((us), ((

let uu___149_9026 = t
in {FStar_Syntax_Syntax.n = uu___149_9026.FStar_Syntax_Syntax.n; FStar_Syntax_Syntax.pos = (FStar_Ident.range_of_lid lid); FStar_Syntax_Syntax.vars = uu___149_9026.FStar_Syntax_Syntax.vars})))), (r)))
end
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end))))


let lid_exists : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____9053 = (lookup_qname env l)
in (match (uu____9053) with
| FStar_Pervasives_Native.None -> begin
false
end
| FStar_Pervasives_Native.Some (uu____9092) -> begin
true
end)))


let lookup_bv : env  ->  FStar_Syntax_Syntax.bv  ->  (FStar_Syntax_Syntax.typ * FStar_Range.range) = (fun env bv -> (

let bvr = (FStar_Syntax_Syntax.range_of_bv bv)
in (

let uu____9142 = (try_lookup_bv env bv)
in (match (uu____9142) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9157 = (

let uu____9158 = (

let uu____9163 = (variable_not_found bv)
in ((uu____9163), (bvr)))
in FStar_Errors.Error (uu____9158))
in (FStar_Exn.raise uu____9157))
end
| FStar_Pervasives_Native.Some (t, r) -> begin
(

let uu____9174 = (FStar_Syntax_Subst.set_use_range bvr t)
in (

let uu____9175 = (

let uu____9176 = (FStar_Range.use_range bvr)
in (FStar_Range.set_use_range r uu____9176))
in ((uu____9174), (uu____9175))))
end))))


let try_lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) FStar_Pervasives_Native.option = (fun env l -> (

let uu____9195 = (try_lookup_lid_aux env l)
in (match (uu____9195) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((us, t), r) -> begin
(

let use_range1 = (FStar_Ident.range_of_lid l)
in (

let r1 = (

let uu____9261 = (FStar_Range.use_range use_range1)
in (FStar_Range.set_use_range r uu____9261))
in (

let uu____9262 = (

let uu____9271 = (

let uu____9276 = (FStar_Syntax_Subst.set_use_range use_range1 t)
in ((us), (uu____9276)))
in ((uu____9271), (r1)))
in FStar_Pervasives_Native.Some (uu____9262))))
end)))


let lookup_lid : env  ->  FStar_Ident.lident  ->  ((FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) * FStar_Range.range) = (fun env l -> (

let uu____9305 = (try_lookup_lid env l)
in (match (uu____9305) with
| FStar_Pervasives_Native.None -> begin
(

let uu____9332 = (

let uu____9333 = (

let uu____9338 = (name_not_found l)
in ((uu____9338), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____9333))
in (FStar_Exn.raise uu____9332))
end
| FStar_Pervasives_Native.Some (v1) -> begin
v1
end)))


let lookup_univ : env  ->  FStar_Syntax_Syntax.univ_name  ->  Prims.bool = (fun env x -> (FStar_All.pipe_right (FStar_List.find (fun uu___133_9376 -> (match (uu___133_9376) with
| Binding_univ (y) -> begin
(Prims.op_Equality x.FStar_Ident.idText y.FStar_Ident.idText)
end
| uu____9378 -> begin
false
end)) env.gamma) FStar_Option.isSome))


let try_lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.tscheme * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env lid -> (

let uu____9395 = (lookup_qname env lid)
in (match (uu____9395) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____9424, uvs, t); FStar_Syntax_Syntax.sigrng = uu____9427; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____9429; FStar_Syntax_Syntax.sigattrs = uu____9430}, FStar_Pervasives_Native.None), uu____9431) -> begin
(

let uu____9480 = (

let uu____9491 = (

let uu____9496 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid) t)
in ((uvs), (uu____9496)))
in ((uu____9491), (q)))
in FStar_Pervasives_Native.Some (uu____9480))
end
| uu____9513 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_val_decl : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____9552 = (lookup_qname env lid)
in (match (uu____9552) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____9577, uvs, t); FStar_Syntax_Syntax.sigrng = uu____9580; FStar_Syntax_Syntax.sigquals = uu____9581; FStar_Syntax_Syntax.sigmeta = uu____9582; FStar_Syntax_Syntax.sigattrs = uu____9583}, FStar_Pervasives_Native.None), uu____9584) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____9633 -> begin
(

let uu____9654 = (

let uu____9655 = (

let uu____9660 = (name_not_found lid)
in ((uu____9660), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____9655))
in (FStar_Exn.raise uu____9654))
end)))


let lookup_datacon : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.universes * FStar_Syntax_Syntax.typ) = (fun env lid -> (

let uu____9677 = (lookup_qname env lid)
in (match (uu____9677) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____9702, uvs, t, uu____9705, uu____9706, uu____9707); FStar_Syntax_Syntax.sigrng = uu____9708; FStar_Syntax_Syntax.sigquals = uu____9709; FStar_Syntax_Syntax.sigmeta = uu____9710; FStar_Syntax_Syntax.sigattrs = uu____9711}, FStar_Pervasives_Native.None), uu____9712) -> begin
(inst_tscheme_with_range (FStar_Ident.range_of_lid lid) ((uvs), (t)))
end
| uu____9765 -> begin
(

let uu____9786 = (

let uu____9787 = (

let uu____9792 = (name_not_found lid)
in ((uu____9792), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____9787))
in (FStar_Exn.raise uu____9786))
end)))


let datacons_of_typ : env  ->  FStar_Ident.lident  ->  (Prims.bool * FStar_Ident.lident Prims.list) = (fun env lid -> (

let uu____9811 = (lookup_qname env lid)
in (match (uu____9811) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____9838, uu____9839, uu____9840, uu____9841, uu____9842, dcs); FStar_Syntax_Syntax.sigrng = uu____9844; FStar_Syntax_Syntax.sigquals = uu____9845; FStar_Syntax_Syntax.sigmeta = uu____9846; FStar_Syntax_Syntax.sigattrs = uu____9847}, uu____9848), uu____9849) -> begin
((true), (dcs))
end
| uu____9910 -> begin
((false), ([]))
end)))


let typ_of_datacon : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (fun env lid -> (

let uu____9941 = (lookup_qname env lid)
in (match (uu____9941) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____9962, uu____9963, uu____9964, l, uu____9966, uu____9967); FStar_Syntax_Syntax.sigrng = uu____9968; FStar_Syntax_Syntax.sigquals = uu____9969; FStar_Syntax_Syntax.sigmeta = uu____9970; FStar_Syntax_Syntax.sigattrs = uu____9971}, uu____9972), uu____9973) -> begin
l
end
| uu____10028 -> begin
(

let uu____10049 = (

let uu____10050 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format1 "Not a datacon: %s" uu____10050))
in (failwith uu____10049))
end)))


let lookup_definition : delta_level Prims.list  ->  env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term) FStar_Pervasives_Native.option = (fun delta_levels env lid -> (

let visible = (fun quals -> (FStar_All.pipe_right delta_levels (FStar_Util.for_some (fun dl -> (FStar_All.pipe_right quals (FStar_Util.for_some (visible_at dl)))))))
in (

let uu____10087 = (lookup_qname env lid)
in (match (uu____10087) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____10115) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_let ((uu____10166, lbs), uu____10168) when (visible se.FStar_Syntax_Syntax.sigquals) -> begin
(FStar_Util.find_map lbs (fun lb -> (

let fv = (FStar_Util.right lb.FStar_Syntax_Syntax.lbname)
in (

let uu____10196 = (FStar_Syntax_Syntax.fv_eq_lid fv lid)
in (match (uu____10196) with
| true -> begin
FStar_Pervasives_Native.Some (((lb.FStar_Syntax_Syntax.lbunivs), (lb.FStar_Syntax_Syntax.lbdef)))
end
| uu____10219 -> begin
FStar_Pervasives_Native.None
end)))))
end
| uu____10228 -> begin
FStar_Pervasives_Native.None
end)
end
| uu____10233 -> begin
FStar_Pervasives_Native.None
end))))


let try_lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env ftv -> (

let uu____10270 = (lookup_qname env ftv)
in (match (uu____10270) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr (se, FStar_Pervasives_Native.None), uu____10294) -> begin
(

let uu____10339 = (effect_signature se)
in (match (uu____10339) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some ((uu____10360, t), r) -> begin
(

let uu____10375 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid ftv) t)
in FStar_Pervasives_Native.Some (uu____10375))
end))
end
| uu____10376 -> begin
FStar_Pervasives_Native.None
end)))


let lookup_effect_lid : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.term = (fun env ftv -> (

let uu____10405 = (try_lookup_effect_lid env ftv)
in (match (uu____10405) with
| FStar_Pervasives_Native.None -> begin
(

let uu____10408 = (

let uu____10409 = (

let uu____10414 = (name_not_found ftv)
in ((uu____10414), ((FStar_Ident.range_of_lid ftv))))
in FStar_Errors.Error (uu____10409))
in (FStar_Exn.raise uu____10408))
end
| FStar_Pervasives_Native.Some (k) -> begin
k
end)))


let lookup_effect_abbrev : env  ->  FStar_Syntax_Syntax.universes  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp) FStar_Pervasives_Native.option = (fun env univ_insts lid0 -> (

let uu____10434 = (lookup_qname env lid0)
in (match (uu____10434) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_effect_abbrev (lid, univs1, binders, c, uu____10465); FStar_Syntax_Syntax.sigrng = uu____10466; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____10468; FStar_Syntax_Syntax.sigattrs = uu____10469}, FStar_Pervasives_Native.None), uu____10470) -> begin
(

let lid1 = (

let uu____10524 = (

let uu____10525 = (FStar_Range.use_range (FStar_Ident.range_of_lid lid0))
in (FStar_Range.set_use_range (FStar_Ident.range_of_lid lid) uu____10525))
in (FStar_Ident.set_lid_range lid uu____10524))
in (

let uu____10526 = (FStar_All.pipe_right quals (FStar_Util.for_some (fun uu___134_10530 -> (match (uu___134_10530) with
| FStar_Syntax_Syntax.Irreducible -> begin
true
end
| uu____10531 -> begin
false
end))))
in (match (uu____10526) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____10542 -> begin
(

let insts = (match ((Prims.op_Equality (FStar_List.length univ_insts) (FStar_List.length univs1))) with
| true -> begin
univ_insts
end
| uu____10544 -> begin
(

let uu____10545 = (

let uu____10546 = (

let uu____10547 = (get_range env)
in (FStar_Range.string_of_range uu____10547))
in (

let uu____10548 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____10549 = (FStar_All.pipe_right (FStar_List.length univ_insts) FStar_Util.string_of_int)
in (FStar_Util.format3 "(%s) Unexpected instantiation of effect %s with %s universes" uu____10546 uu____10548 uu____10549))))
in (failwith uu____10545))
end)
in (match (((binders), (univs1))) with
| ([], uu____10556) -> begin
(failwith "Unexpected effect abbreviation with no arguments")
end
| (uu____10573, (uu____10574)::(uu____10575)::uu____10576) -> begin
(

let uu____10581 = (

let uu____10582 = (FStar_Syntax_Print.lid_to_string lid1)
in (

let uu____10583 = (FStar_All.pipe_left FStar_Util.string_of_int (FStar_List.length univs1))
in (FStar_Util.format2 "Unexpected effect abbreviation %s; polymorphic in %s universes" uu____10582 uu____10583)))
in (failwith uu____10581))
end
| uu____10590 -> begin
(

let uu____10595 = (

let uu____10600 = (

let uu____10601 = (FStar_Syntax_Util.arrow binders c)
in ((univs1), (uu____10601)))
in (inst_tscheme_with uu____10600 insts))
in (match (uu____10595) with
| (uu____10612, t) -> begin
(

let t1 = (FStar_Syntax_Subst.set_use_range (FStar_Ident.range_of_lid lid1) t)
in (

let uu____10615 = (

let uu____10616 = (FStar_Syntax_Subst.compress t1)
in uu____10616.FStar_Syntax_Syntax.n)
in (match (uu____10615) with
| FStar_Syntax_Syntax.Tm_arrow (binders1, c1) -> begin
FStar_Pervasives_Native.Some (((binders1), (c1)))
end
| uu____10663 -> begin
(failwith "Impossible")
end)))
end))
end))
end)))
end
| uu____10670 -> begin
FStar_Pervasives_Native.None
end)))


let norm_eff_name : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident = (

let cache = (FStar_Util.smap_create (Prims.parse_int "20"))
in (fun env l -> (

let rec find1 = (fun l1 -> (

let uu____10712 = (lookup_effect_abbrev env ((FStar_Syntax_Syntax.U_unknown)::[]) l1)
in (match (uu____10712) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (uu____10725, c) -> begin
(

let l2 = (FStar_Syntax_Util.comp_effect_name c)
in (

let uu____10732 = (find1 l2)
in (match (uu____10732) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (l2)
end
| FStar_Pervasives_Native.Some (l') -> begin
FStar_Pervasives_Native.Some (l')
end)))
end)))
in (

let res = (

let uu____10739 = (FStar_Util.smap_try_find cache l.FStar_Ident.str)
in (match (uu____10739) with
| FStar_Pervasives_Native.Some (l1) -> begin
l1
end
| FStar_Pervasives_Native.None -> begin
(

let uu____10743 = (find1 l)
in (match (uu____10743) with
| FStar_Pervasives_Native.None -> begin
l
end
| FStar_Pervasives_Native.Some (m) -> begin
((FStar_Util.smap_add cache l.FStar_Ident.str m);
m;
)
end))
end))
in (FStar_Ident.set_lid_range res (FStar_Ident.range_of_lid l))))))


let lookup_effect_quals : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.qualifier Prims.list = (fun env l -> (

let l1 = (norm_eff_name env l)
in (

let uu____10759 = (lookup_qname env l1)
in (match (uu____10759) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_new_effect (uu____10782); FStar_Syntax_Syntax.sigrng = uu____10783; FStar_Syntax_Syntax.sigquals = q; FStar_Syntax_Syntax.sigmeta = uu____10785; FStar_Syntax_Syntax.sigattrs = uu____10786}, uu____10787), uu____10788) -> begin
q
end
| uu____10839 -> begin
[]
end))))


let lookup_projector : env  ->  FStar_Ident.lident  ->  Prims.int  ->  FStar_Ident.lident = (fun env lid i -> (

let fail = (fun uu____10875 -> (

let uu____10876 = (

let uu____10877 = (FStar_Util.string_of_int i)
in (

let uu____10878 = (FStar_Syntax_Print.lid_to_string lid)
in (FStar_Util.format2 "Impossible: projecting field #%s from constructor %s is undefined" uu____10877 uu____10878)))
in (failwith uu____10876)))
in (

let uu____10879 = (lookup_datacon env lid)
in (match (uu____10879) with
| (uu____10884, t) -> begin
(

let uu____10886 = (

let uu____10887 = (FStar_Syntax_Subst.compress t)
in uu____10887.FStar_Syntax_Syntax.n)
in (match (uu____10886) with
| FStar_Syntax_Syntax.Tm_arrow (binders, uu____10891) -> begin
(match (((i < (Prims.parse_int "0")) || (i >= (FStar_List.length binders)))) with
| true -> begin
(fail ())
end
| uu____10912 -> begin
(

let b = (FStar_List.nth binders i)
in (

let uu____10922 = (FStar_Syntax_Util.mk_field_projector_name lid (FStar_Pervasives_Native.fst b) i)
in (FStar_All.pipe_right uu____10922 FStar_Pervasives_Native.fst)))
end)
end
| uu____10931 -> begin
(fail ())
end))
end))))


let is_projector : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env l -> (

let uu____10940 = (lookup_qname env l)
in (match (uu____10940) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_declare_typ (uu____10961, uu____10962, uu____10963); FStar_Syntax_Syntax.sigrng = uu____10964; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____10966; FStar_Syntax_Syntax.sigattrs = uu____10967}, uu____10968), uu____10969) -> begin
(FStar_Util.for_some (fun uu___135_11022 -> (match (uu___135_11022) with
| FStar_Syntax_Syntax.Projector (uu____11023) -> begin
true
end
| uu____11028 -> begin
false
end)) quals)
end
| uu____11029 -> begin
false
end)))


let is_datacon : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____11058 = (lookup_qname env lid)
in (match (uu____11058) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon (uu____11079, uu____11080, uu____11081, uu____11082, uu____11083, uu____11084); FStar_Syntax_Syntax.sigrng = uu____11085; FStar_Syntax_Syntax.sigquals = uu____11086; FStar_Syntax_Syntax.sigmeta = uu____11087; FStar_Syntax_Syntax.sigattrs = uu____11088}, uu____11089), uu____11090) -> begin
true
end
| uu____11145 -> begin
false
end)))


let is_record : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____11174 = (lookup_qname env lid)
in (match (uu____11174) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____11195, uu____11196, uu____11197, uu____11198, uu____11199, uu____11200); FStar_Syntax_Syntax.sigrng = uu____11201; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____11203; FStar_Syntax_Syntax.sigattrs = uu____11204}, uu____11205), uu____11206) -> begin
(FStar_Util.for_some (fun uu___136_11267 -> (match (uu___136_11267) with
| FStar_Syntax_Syntax.RecordType (uu____11268) -> begin
true
end
| FStar_Syntax_Syntax.RecordConstructor (uu____11277) -> begin
true
end
| uu____11286 -> begin
false
end)) quals)
end
| uu____11287 -> begin
false
end)))


let is_action : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____11316 = (lookup_qname env lid)
in (match (uu____11316) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_let (uu____11337, uu____11338); FStar_Syntax_Syntax.sigrng = uu____11339; FStar_Syntax_Syntax.sigquals = quals; FStar_Syntax_Syntax.sigmeta = uu____11341; FStar_Syntax_Syntax.sigattrs = uu____11342}, uu____11343), uu____11344) -> begin
(FStar_Util.for_some (fun uu___137_11401 -> (match (uu___137_11401) with
| FStar_Syntax_Syntax.Action (uu____11402) -> begin
true
end
| uu____11403 -> begin
false
end)) quals)
end
| uu____11404 -> begin
false
end)))


let is_interpreted : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (

let interpreted_symbols = (FStar_Parser_Const.op_Eq)::(FStar_Parser_Const.op_notEq)::(FStar_Parser_Const.op_LT)::(FStar_Parser_Const.op_LTE)::(FStar_Parser_Const.op_GT)::(FStar_Parser_Const.op_GTE)::(FStar_Parser_Const.op_Subtraction)::(FStar_Parser_Const.op_Minus)::(FStar_Parser_Const.op_Addition)::(FStar_Parser_Const.op_Multiply)::(FStar_Parser_Const.op_Division)::(FStar_Parser_Const.op_Modulus)::(FStar_Parser_Const.op_And)::(FStar_Parser_Const.op_Or)::(FStar_Parser_Const.op_Negation)::[]
in (fun env head1 -> (

let uu____11436 = (

let uu____11437 = (FStar_Syntax_Util.un_uinst head1)
in uu____11437.FStar_Syntax_Syntax.n)
in (match (uu____11436) with
| FStar_Syntax_Syntax.Tm_fvar (fv) -> begin
(Prims.op_Equality fv.FStar_Syntax_Syntax.fv_delta FStar_Syntax_Syntax.Delta_equational)
end
| uu____11441 -> begin
false
end))))


let is_type_constructor : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let mapper = (fun x -> (match ((FStar_Pervasives_Native.fst x)) with
| FStar_Util.Inl (uu____11508) -> begin
FStar_Pervasives_Native.Some (false)
end
| FStar_Util.Inr (se, uu____11524) -> begin
(match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_declare_typ (uu____11541) -> begin
FStar_Pervasives_Native.Some ((FStar_List.contains FStar_Syntax_Syntax.New se.FStar_Syntax_Syntax.sigquals))
end
| FStar_Syntax_Syntax.Sig_inductive_typ (uu____11548) -> begin
FStar_Pervasives_Native.Some (true)
end
| uu____11565 -> begin
FStar_Pervasives_Native.Some (false)
end)
end))
in (

let uu____11566 = (

let uu____11569 = (lookup_qname env lid)
in (FStar_Util.bind_opt uu____11569 mapper))
in (match (uu____11566) with
| FStar_Pervasives_Native.Some (b) -> begin
b
end
| FStar_Pervasives_Native.None -> begin
false
end))))


let num_inductive_ty_params : env  ->  FStar_Ident.lident  ->  Prims.int = (fun env lid -> (

let uu____11617 = (lookup_qname env lid)
in (match (uu____11617) with
| FStar_Pervasives_Native.Some (FStar_Util.Inr ({FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_inductive_typ (uu____11638, uu____11639, tps, uu____11641, uu____11642, uu____11643); FStar_Syntax_Syntax.sigrng = uu____11644; FStar_Syntax_Syntax.sigquals = uu____11645; FStar_Syntax_Syntax.sigmeta = uu____11646; FStar_Syntax_Syntax.sigattrs = uu____11647}, uu____11648), uu____11649) -> begin
(FStar_List.length tps)
end
| uu____11712 -> begin
(

let uu____11733 = (

let uu____11734 = (

let uu____11739 = (name_not_found lid)
in ((uu____11739), ((FStar_Ident.range_of_lid lid))))
in FStar_Errors.Error (uu____11734))
in (FStar_Exn.raise uu____11733))
end)))


let effect_decl_opt : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.eff_decl * FStar_Syntax_Syntax.qualifier Prims.list) FStar_Pervasives_Native.option = (fun env l -> (FStar_All.pipe_right env.effects.decls (FStar_Util.find_opt (fun uu____11781 -> (match (uu____11781) with
| (d, uu____11789) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname l)
end)))))


let get_effect_decl : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.eff_decl = (fun env l -> (

let uu____11802 = (effect_decl_opt env l)
in (match (uu____11802) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11817 = (

let uu____11818 = (

let uu____11823 = (name_not_found l)
in ((uu____11823), ((FStar_Ident.range_of_lid l))))
in FStar_Errors.Error (uu____11818))
in (FStar_Exn.raise uu____11817))
end
| FStar_Pervasives_Native.Some (md) -> begin
(FStar_Pervasives_Native.fst md)
end)))


let identity_mlift : mlift = {mlift_wp = (fun t wp -> wp); mlift_term = FStar_Pervasives_Native.Some ((fun t wp e -> (FStar_Util.return_all e)))}


let join : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  (FStar_Ident.lident * mlift * mlift) = (fun env l1 l2 -> (match ((FStar_Ident.lid_equals l1 l2)) with
| true -> begin
((l1), (identity_mlift), (identity_mlift))
end
| uu____11881 -> begin
(match ((((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_Tot_lid)) || ((FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid) && (FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid)))) with
| true -> begin
((FStar_Parser_Const.effect_GTot_lid), (identity_mlift), (identity_mlift))
end
| uu____11888 -> begin
(

let uu____11889 = (FStar_All.pipe_right env.effects.joins (FStar_Util.find_opt (fun uu____11942 -> (match (uu____11942) with
| (m1, m2, uu____11955, uu____11956, uu____11957) -> begin
((FStar_Ident.lid_equals l1 m1) && (FStar_Ident.lid_equals l2 m2))
end))))
in (match (uu____11889) with
| FStar_Pervasives_Native.None -> begin
(

let uu____11974 = (

let uu____11975 = (

let uu____11980 = (

let uu____11981 = (FStar_Syntax_Print.lid_to_string l1)
in (

let uu____11982 = (FStar_Syntax_Print.lid_to_string l2)
in (FStar_Util.format2 "Effects %s and %s cannot be composed" uu____11981 uu____11982)))
in ((uu____11980), (env.range)))
in FStar_Errors.Error (uu____11975))
in (FStar_Exn.raise uu____11974))
end
| FStar_Pervasives_Native.Some (uu____11989, uu____11990, m3, j1, j2) -> begin
((m3), (j1), (j2))
end))
end)
end))


let monad_leq : env  ->  FStar_Ident.lident  ->  FStar_Ident.lident  ->  edge FStar_Pervasives_Native.option = (fun env l1 l2 -> (match (((FStar_Ident.lid_equals l1 l2) || ((FStar_Ident.lid_equals l1 FStar_Parser_Const.effect_Tot_lid) && (FStar_Ident.lid_equals l2 FStar_Parser_Const.effect_GTot_lid)))) with
| true -> begin
FStar_Pervasives_Native.Some ({msource = l1; mtarget = l2; mlift = identity_mlift})
end
| uu____12020 -> begin
(FStar_All.pipe_right env.effects.order (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals l1 e.msource) && (FStar_Ident.lid_equals l2 e.mtarget)))))
end))


let wp_sig_aux : 'Auu____12033 . (FStar_Syntax_Syntax.eff_decl * 'Auu____12033) Prims.list  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax) = (fun decls m -> (

let uu____12060 = (FStar_All.pipe_right decls (FStar_Util.find_opt (fun uu____12086 -> (match (uu____12086) with
| (d, uu____12092) -> begin
(FStar_Ident.lid_equals d.FStar_Syntax_Syntax.mname m)
end))))
in (match (uu____12060) with
| FStar_Pervasives_Native.None -> begin
(

let uu____12103 = (FStar_Util.format1 "Impossible: declaration for monad %s not found" m.FStar_Ident.str)
in (failwith uu____12103))
end
| FStar_Pervasives_Native.Some (md, _q) -> begin
(

let uu____12116 = (inst_tscheme ((md.FStar_Syntax_Syntax.univs), (md.FStar_Syntax_Syntax.signature)))
in (match (uu____12116) with
| (uu____12127, s) -> begin
(

let s1 = (FStar_Syntax_Subst.compress s)
in (match (((md.FStar_Syntax_Syntax.binders), (s1.FStar_Syntax_Syntax.n))) with
| ([], FStar_Syntax_Syntax.Tm_arrow (((a, uu____12137))::((wp, uu____12139))::[], c)) when (FStar_Syntax_Syntax.is_teff (FStar_Syntax_Util.comp_result c)) -> begin
((a), (wp.FStar_Syntax_Syntax.sort))
end
| uu____12175 -> begin
(failwith "Impossible")
end))
end))
end)))


let wp_signature : env  ->  FStar_Ident.lident  ->  (FStar_Syntax_Syntax.bv * FStar_Syntax_Syntax.term) = (fun env m -> (wp_sig_aux env.effects.decls m))


let null_wp_for_eff : env  ->  FStar_Ident.lident  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term  ->  FStar_Syntax_Syntax.comp = (fun env eff_name res_u res_t -> (match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_Tot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_Total' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____12216 -> begin
(match ((FStar_Ident.lid_equals eff_name FStar_Parser_Const.effect_GTot_lid)) with
| true -> begin
(FStar_Syntax_Syntax.mk_GTotal' res_t (FStar_Pervasives_Native.Some (res_u)))
end
| uu____12217 -> begin
(

let eff_name1 = (norm_eff_name env eff_name)
in (

let ed = (get_effect_decl env eff_name1)
in (

let null_wp = (inst_effect_fun_with ((res_u)::[]) env ed ed.FStar_Syntax_Syntax.null_wp)
in (

let null_wp_res = (

let uu____12224 = (get_range env)
in (

let uu____12225 = (

let uu____12228 = (

let uu____12229 = (

let uu____12244 = (

let uu____12247 = (FStar_Syntax_Syntax.as_arg res_t)
in (uu____12247)::[])
in ((null_wp), (uu____12244)))
in FStar_Syntax_Syntax.Tm_app (uu____12229))
in (FStar_Syntax_Syntax.mk uu____12228))
in (uu____12225 FStar_Pervasives_Native.None uu____12224)))
in (

let uu____12253 = (

let uu____12254 = (

let uu____12263 = (FStar_Syntax_Syntax.as_arg null_wp_res)
in (uu____12263)::[])
in {FStar_Syntax_Syntax.comp_univs = (res_u)::[]; FStar_Syntax_Syntax.effect_name = eff_name1; FStar_Syntax_Syntax.result_typ = res_t; FStar_Syntax_Syntax.effect_args = uu____12254; FStar_Syntax_Syntax.flags = []})
in (FStar_Syntax_Syntax.mk_Comp uu____12253))))))
end)
end))


let build_lattice : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env se -> (match (se.FStar_Syntax_Syntax.sigel) with
| FStar_Syntax_Syntax.Sig_new_effect (ne) -> begin
(

let effects = (

let uu___150_12274 = env.effects
in {decls = (((ne), (se.FStar_Syntax_Syntax.sigquals)))::env.effects.decls; order = uu___150_12274.order; joins = uu___150_12274.joins})
in (

let uu___151_12283 = env
in {solver = uu___151_12283.solver; range = uu___151_12283.range; curmodule = uu___151_12283.curmodule; gamma = uu___151_12283.gamma; gamma_cache = uu___151_12283.gamma_cache; modules = uu___151_12283.modules; expected_typ = uu___151_12283.expected_typ; sigtab = uu___151_12283.sigtab; is_pattern = uu___151_12283.is_pattern; instantiate_imp = uu___151_12283.instantiate_imp; effects = effects; generalize = uu___151_12283.generalize; letrecs = uu___151_12283.letrecs; top_level = uu___151_12283.top_level; check_uvars = uu___151_12283.check_uvars; use_eq = uu___151_12283.use_eq; is_iface = uu___151_12283.is_iface; admit = uu___151_12283.admit; lax = uu___151_12283.lax; lax_universes = uu___151_12283.lax_universes; failhard = uu___151_12283.failhard; nosynth = uu___151_12283.nosynth; tc_term = uu___151_12283.tc_term; type_of = uu___151_12283.type_of; universe_of = uu___151_12283.universe_of; use_bv_sorts = uu___151_12283.use_bv_sorts; qname_and_index = uu___151_12283.qname_and_index; proof_ns = uu___151_12283.proof_ns; synth = uu___151_12283.synth; is_native_tactic = uu___151_12283.is_native_tactic; identifier_info = uu___151_12283.identifier_info; tc_hooks = uu___151_12283.tc_hooks; dsenv = uu___151_12283.dsenv}))
end
| FStar_Syntax_Syntax.Sig_sub_effect (sub1) -> begin
(

let compose_edges = (fun e1 e2 -> (

let composed_lift = (

let mlift_wp = (fun r wp1 -> (

let uu____12300 = (e1.mlift.mlift_wp r wp1)
in (e2.mlift.mlift_wp r uu____12300)))
in (

let mlift_term = (match (((e1.mlift.mlift_term), (e2.mlift.mlift_term))) with
| (FStar_Pervasives_Native.Some (l1), FStar_Pervasives_Native.Some (l2)) -> begin
FStar_Pervasives_Native.Some ((fun t wp e -> (

let uu____12390 = (e1.mlift.mlift_wp t wp)
in (

let uu____12391 = (l1 t wp e)
in (l2 t uu____12390 uu____12391)))))
end
| uu____12392 -> begin
FStar_Pervasives_Native.None
end)
in {mlift_wp = mlift_wp; mlift_term = mlift_term}))
in {msource = e1.msource; mtarget = e2.mtarget; mlift = composed_lift}))
in (

let mk_mlift_wp = (fun lift_t r wp1 -> (

let uu____12431 = (inst_tscheme lift_t)
in (match (uu____12431) with
| (uu____12438, lift_t1) -> begin
(

let uu____12440 = (

let uu____12443 = (

let uu____12444 = (

let uu____12459 = (

let uu____12462 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____12463 = (

let uu____12466 = (FStar_Syntax_Syntax.as_arg wp1)
in (uu____12466)::[])
in (uu____12462)::uu____12463))
in ((lift_t1), (uu____12459)))
in FStar_Syntax_Syntax.Tm_app (uu____12444))
in (FStar_Syntax_Syntax.mk uu____12443))
in (uu____12440 FStar_Pervasives_Native.None wp1.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_mlift_wp = (match (sub1.FStar_Syntax_Syntax.lift_wp) with
| FStar_Pervasives_Native.Some (sub_lift_wp) -> begin
(mk_mlift_wp sub_lift_wp)
end
| FStar_Pervasives_Native.None -> begin
(failwith "sub effect should\'ve been elaborated at this stage")
end)
in (

let mk_mlift_term = (fun lift_t r wp1 e -> (

let uu____12507 = (inst_tscheme lift_t)
in (match (uu____12507) with
| (uu____12514, lift_t1) -> begin
(

let uu____12516 = (

let uu____12519 = (

let uu____12520 = (

let uu____12535 = (

let uu____12538 = (FStar_Syntax_Syntax.as_arg r)
in (

let uu____12539 = (

let uu____12542 = (FStar_Syntax_Syntax.as_arg wp1)
in (

let uu____12543 = (

let uu____12546 = (FStar_Syntax_Syntax.as_arg e)
in (uu____12546)::[])
in (uu____12542)::uu____12543))
in (uu____12538)::uu____12539))
in ((lift_t1), (uu____12535)))
in FStar_Syntax_Syntax.Tm_app (uu____12520))
in (FStar_Syntax_Syntax.mk uu____12519))
in (uu____12516 FStar_Pervasives_Native.None e.FStar_Syntax_Syntax.pos))
end)))
in (

let sub_mlift_term = (FStar_Util.map_opt sub1.FStar_Syntax_Syntax.lift mk_mlift_term)
in (

let edge = {msource = sub1.FStar_Syntax_Syntax.source; mtarget = sub1.FStar_Syntax_Syntax.target; mlift = {mlift_wp = sub_mlift_wp; mlift_term = sub_mlift_term}}
in (

let id_edge = (fun l -> {msource = sub1.FStar_Syntax_Syntax.source; mtarget = sub1.FStar_Syntax_Syntax.target; mlift = identity_mlift})
in (

let print_mlift = (fun l -> (

let bogus_term = (fun s -> (

let uu____12584 = (

let uu____12585 = (FStar_Ident.lid_of_path ((s)::[]) FStar_Range.dummyRange)
in (FStar_Syntax_Syntax.lid_as_fv uu____12585 FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None))
in (FStar_Syntax_Syntax.fv_to_tm uu____12584)))
in (

let arg = (bogus_term "ARG")
in (

let wp = (bogus_term "WP")
in (

let e = (bogus_term "COMP")
in (

let uu____12589 = (

let uu____12590 = (l.mlift_wp arg wp)
in (FStar_Syntax_Print.term_to_string uu____12590))
in (

let uu____12591 = (

let uu____12592 = (FStar_Util.map_opt l.mlift_term (fun l1 -> (

let uu____12610 = (l1 arg wp e)
in (FStar_Syntax_Print.term_to_string uu____12610))))
in (FStar_Util.dflt "none" uu____12592))
in (FStar_Util.format2 "{ wp : %s ; term : %s }" uu____12589 uu____12591))))))))
in (

let order = (edge)::env.effects.order
in (

let ms = (FStar_All.pipe_right env.effects.decls (FStar_List.map (fun uu____12636 -> (match (uu____12636) with
| (e, uu____12644) -> begin
e.FStar_Syntax_Syntax.mname
end))))
in (

let find_edge = (fun order1 uu____12663 -> (match (uu____12663) with
| (i, j) -> begin
(match ((FStar_Ident.lid_equals i j)) with
| true -> begin
(FStar_All.pipe_right (id_edge i) (fun _0_41 -> FStar_Pervasives_Native.Some (_0_41)))
end
| uu____12678 -> begin
(FStar_All.pipe_right order1 (FStar_Util.find_opt (fun e -> ((FStar_Ident.lid_equals e.msource i) && (FStar_Ident.lid_equals e.mtarget j)))))
end)
end))
in (

let order1 = (

let fold_fun = (fun order1 k -> (

let uu____12701 = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (match ((FStar_Ident.lid_equals i k)) with
| true -> begin
[]
end
| uu____12712 -> begin
(FStar_All.pipe_right ms (FStar_List.collect (fun j -> (match ((FStar_Ident.lid_equals j k)) with
| true -> begin
[]
end
| uu____12721 -> begin
(

let uu____12722 = (

let uu____12731 = (find_edge order1 ((i), (k)))
in (

let uu____12734 = (find_edge order1 ((k), (j)))
in ((uu____12731), (uu____12734))))
in (match (uu____12722) with
| (FStar_Pervasives_Native.Some (e1), FStar_Pervasives_Native.Some (e2)) -> begin
(

let uu____12749 = (compose_edges e1 e2)
in (uu____12749)::[])
end
| uu____12750 -> begin
[]
end))
end))))
end))))
in (FStar_List.append order1 uu____12701)))
in (FStar_All.pipe_right ms (FStar_List.fold_left fold_fun order)))
in (

let order2 = (FStar_Util.remove_dups (fun e1 e2 -> ((FStar_Ident.lid_equals e1.msource e2.msource) && (FStar_Ident.lid_equals e1.mtarget e2.mtarget))) order1)
in ((FStar_All.pipe_right order2 (FStar_List.iter (fun edge1 -> (

let uu____12779 = ((FStar_Ident.lid_equals edge1.msource FStar_Parser_Const.effect_DIV_lid) && (

let uu____12781 = (lookup_effect_quals env edge1.mtarget)
in (FStar_All.pipe_right uu____12781 (FStar_List.contains FStar_Syntax_Syntax.TotalEffect))))
in (match (uu____12779) with
| true -> begin
(

let uu____12786 = (

let uu____12787 = (

let uu____12792 = (FStar_Util.format1 "Divergent computations cannot be included in an effect %s marked \'total\'" edge1.mtarget.FStar_Ident.str)
in (

let uu____12793 = (get_range env)
in ((uu____12792), (uu____12793))))
in FStar_Errors.Error (uu____12787))
in (FStar_Exn.raise uu____12786))
end
| uu____12794 -> begin
()
end)))));
(

let joins = (FStar_All.pipe_right ms (FStar_List.collect (fun i -> (FStar_All.pipe_right ms (FStar_List.collect (fun j -> (

let join_opt = (match ((FStar_Ident.lid_equals i j)) with
| true -> begin
FStar_Pervasives_Native.Some (((i), ((id_edge i)), ((id_edge i))))
end
| uu____12884 -> begin
(FStar_All.pipe_right ms (FStar_List.fold_left (fun bopt k -> (

let uu____12918 = (

let uu____12927 = (find_edge order2 ((i), (k)))
in (

let uu____12930 = (find_edge order2 ((j), (k)))
in ((uu____12927), (uu____12930))))
in (match (uu____12918) with
| (FStar_Pervasives_Native.Some (ik), FStar_Pervasives_Native.Some (jk)) -> begin
(match (bopt) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| FStar_Pervasives_Native.Some (ub, uu____12972, uu____12973) -> begin
(

let uu____12980 = (

let uu____12985 = (

let uu____12986 = (find_edge order2 ((k), (ub)))
in (FStar_Util.is_some uu____12986))
in (

let uu____12989 = (

let uu____12990 = (find_edge order2 ((ub), (k)))
in (FStar_Util.is_some uu____12990))
in ((uu____12985), (uu____12989))))
in (match (uu____12980) with
| (true, true) -> begin
(match ((FStar_Ident.lid_equals k ub)) with
| true -> begin
((FStar_Util.print_warning "Looking multiple times at the same upper bound candidate\n");
bopt;
)
end
| uu____13010 -> begin
(failwith "Found a cycle in the lattice")
end)
end
| (false, false) -> begin
bopt
end
| (true, false) -> begin
FStar_Pervasives_Native.Some (((k), (ik), (jk)))
end
| (false, true) -> begin
bopt
end))
end)
end
| uu____13025 -> begin
bopt
end))) FStar_Pervasives_Native.None))
end)
in (match (join_opt) with
| FStar_Pervasives_Native.None -> begin
[]
end
| FStar_Pervasives_Native.Some (k, e1, e2) -> begin
(((i), (j), (k), (e1.mlift), (e2.mlift)))::[]
end))))))))
in (

let effects = (

let uu___152_13098 = env.effects
in {decls = uu___152_13098.decls; order = order2; joins = joins})
in (

let uu___153_13099 = env
in {solver = uu___153_13099.solver; range = uu___153_13099.range; curmodule = uu___153_13099.curmodule; gamma = uu___153_13099.gamma; gamma_cache = uu___153_13099.gamma_cache; modules = uu___153_13099.modules; expected_typ = uu___153_13099.expected_typ; sigtab = uu___153_13099.sigtab; is_pattern = uu___153_13099.is_pattern; instantiate_imp = uu___153_13099.instantiate_imp; effects = effects; generalize = uu___153_13099.generalize; letrecs = uu___153_13099.letrecs; top_level = uu___153_13099.top_level; check_uvars = uu___153_13099.check_uvars; use_eq = uu___153_13099.use_eq; is_iface = uu___153_13099.is_iface; admit = uu___153_13099.admit; lax = uu___153_13099.lax; lax_universes = uu___153_13099.lax_universes; failhard = uu___153_13099.failhard; nosynth = uu___153_13099.nosynth; tc_term = uu___153_13099.tc_term; type_of = uu___153_13099.type_of; universe_of = uu___153_13099.universe_of; use_bv_sorts = uu___153_13099.use_bv_sorts; qname_and_index = uu___153_13099.qname_and_index; proof_ns = uu___153_13099.proof_ns; synth = uu___153_13099.synth; is_native_tactic = uu___153_13099.is_native_tactic; identifier_info = uu___153_13099.identifier_info; tc_hooks = uu___153_13099.tc_hooks; dsenv = uu___153_13099.dsenv})));
))))))))))))))
end
| uu____13100 -> begin
env
end))


let comp_to_comp_typ : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env c -> (

let c1 = (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Total (t, FStar_Pervasives_Native.None) -> begin
(

let u = (env.universe_of env t)
in (FStar_Syntax_Syntax.mk_Total' t (FStar_Pervasives_Native.Some (u))))
end
| FStar_Syntax_Syntax.GTotal (t, FStar_Pervasives_Native.None) -> begin
(

let u = (env.universe_of env t)
in (FStar_Syntax_Syntax.mk_GTotal' t (FStar_Pervasives_Native.Some (u))))
end
| uu____13126 -> begin
c
end)
in (FStar_Syntax_Util.comp_to_comp_typ c1)))


let rec unfold_effect_abbrev : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.comp_typ = (fun env comp -> (

let c = (comp_to_comp_typ env comp)
in (

let uu____13136 = (lookup_effect_abbrev env c.FStar_Syntax_Syntax.comp_univs c.FStar_Syntax_Syntax.effect_name)
in (match (uu____13136) with
| FStar_Pervasives_Native.None -> begin
c
end
| FStar_Pervasives_Native.Some (binders, cdef) -> begin
(

let uu____13153 = (FStar_Syntax_Subst.open_comp binders cdef)
in (match (uu____13153) with
| (binders1, cdef1) -> begin
((match ((Prims.op_disEquality (FStar_List.length binders1) ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))) with
| true -> begin
(

let uu____13171 = (

let uu____13172 = (

let uu____13177 = (

let uu____13178 = (FStar_Util.string_of_int (FStar_List.length binders1))
in (

let uu____13183 = (FStar_Util.string_of_int ((FStar_List.length c.FStar_Syntax_Syntax.effect_args) + (Prims.parse_int "1")))
in (

let uu____13190 = (

let uu____13191 = (FStar_Syntax_Syntax.mk_Comp c)
in (FStar_Syntax_Print.comp_to_string uu____13191))
in (FStar_Util.format3 "Effect constructor is not fully applied; expected %s args, got %s args, i.e., %s" uu____13178 uu____13183 uu____13190))))
in ((uu____13177), (comp.FStar_Syntax_Syntax.pos)))
in FStar_Errors.Error (uu____13172))
in (FStar_Exn.raise uu____13171))
end
| uu____13192 -> begin
()
end);
(

let inst1 = (

let uu____13196 = (

let uu____13205 = (FStar_Syntax_Syntax.as_arg c.FStar_Syntax_Syntax.result_typ)
in (uu____13205)::c.FStar_Syntax_Syntax.effect_args)
in (FStar_List.map2 (fun uu____13222 uu____13223 -> (match (((uu____13222), (uu____13223))) with
| ((x, uu____13245), (t, uu____13247)) -> begin
FStar_Syntax_Syntax.NT (((x), (t)))
end)) binders1 uu____13196))
in (

let c1 = (FStar_Syntax_Subst.subst_comp inst1 cdef1)
in (

let c2 = (

let uu____13266 = (

let uu___154_13267 = (comp_to_comp_typ env c1)
in {FStar_Syntax_Syntax.comp_univs = uu___154_13267.FStar_Syntax_Syntax.comp_univs; FStar_Syntax_Syntax.effect_name = uu___154_13267.FStar_Syntax_Syntax.effect_name; FStar_Syntax_Syntax.result_typ = uu___154_13267.FStar_Syntax_Syntax.result_typ; FStar_Syntax_Syntax.effect_args = uu___154_13267.FStar_Syntax_Syntax.effect_args; FStar_Syntax_Syntax.flags = c.FStar_Syntax_Syntax.flags})
in (FStar_All.pipe_right uu____13266 FStar_Syntax_Syntax.mk_Comp))
in (unfold_effect_abbrev env c2))));
)
end))
end))))


let effect_repr_aux : Prims.bool  ->  env  ->  FStar_Syntax_Syntax.comp' FStar_Syntax_Syntax.syntax  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax FStar_Pervasives_Native.option = (fun only_reifiable env c u_c -> (

let effect_name = (norm_eff_name env (FStar_Syntax_Util.comp_effect_name c))
in (

let uu____13293 = (effect_decl_opt env effect_name)
in (match (uu____13293) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (ed, qualifiers) -> begin
(

let uu____13326 = (only_reifiable && (

let uu____13328 = (FStar_All.pipe_right qualifiers (FStar_List.contains FStar_Syntax_Syntax.Reifiable))
in (not (uu____13328))))
in (match (uu____13326) with
| true -> begin
FStar_Pervasives_Native.None
end
| uu____13337 -> begin
(match (ed.FStar_Syntax_Syntax.repr.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Tm_unknown -> begin
FStar_Pervasives_Native.None
end
| uu____13344 -> begin
(

let c1 = (unfold_effect_abbrev env c)
in (

let res_typ = c1.FStar_Syntax_Syntax.result_typ
in (

let wp = (match (c1.FStar_Syntax_Syntax.effect_args) with
| (hd1)::uu____13363 -> begin
hd1
end
| [] -> begin
(

let name = (FStar_Ident.string_of_lid effect_name)
in (

let message = (

let uu____13392 = (FStar_Util.format1 "Not enough arguments for effect %s. " name)
in (Prims.strcat uu____13392 (Prims.strcat "This usually happens when you use a partially applied DM4F effect, " "like [TAC int] instead of [Tac int].")))
in (

let uu____13393 = (

let uu____13394 = (

let uu____13399 = (get_range env)
in ((message), (uu____13399)))
in FStar_Errors.Error (uu____13394))
in (FStar_Exn.raise uu____13393))))
end)
in (

let repr = (inst_effect_fun_with ((u_c)::[]) env ed (([]), (ed.FStar_Syntax_Syntax.repr)))
in (

let uu____13409 = (

let uu____13412 = (get_range env)
in (

let uu____13413 = (

let uu____13416 = (

let uu____13417 = (

let uu____13432 = (

let uu____13435 = (FStar_Syntax_Syntax.as_arg res_typ)
in (uu____13435)::(wp)::[])
in ((repr), (uu____13432)))
in FStar_Syntax_Syntax.Tm_app (uu____13417))
in (FStar_Syntax_Syntax.mk uu____13416))
in (uu____13413 FStar_Pervasives_Native.None uu____13412)))
in FStar_Pervasives_Native.Some (uu____13409))))))
end)
end))
end))))


let effect_repr : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term FStar_Pervasives_Native.option = (fun env c u_c -> (effect_repr_aux false env c u_c))


let reify_comp : env  ->  FStar_Syntax_Syntax.comp  ->  FStar_Syntax_Syntax.universe  ->  FStar_Syntax_Syntax.term = (fun env c u_c -> (

let no_reify = (fun l -> (

let uu____13487 = (

let uu____13488 = (

let uu____13493 = (

let uu____13494 = (FStar_Ident.string_of_lid l)
in (FStar_Util.format1 "Effect %s cannot be reified" uu____13494))
in (

let uu____13495 = (get_range env)
in ((uu____13493), (uu____13495))))
in FStar_Errors.Error (uu____13488))
in (FStar_Exn.raise uu____13487)))
in (

let uu____13496 = (effect_repr_aux true env c u_c)
in (match (uu____13496) with
| FStar_Pervasives_Native.None -> begin
(no_reify (FStar_Syntax_Util.comp_effect_name c))
end
| FStar_Pervasives_Native.Some (tm) -> begin
tm
end))))


let is_reifiable_effect : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env effect_lid -> (

let quals = (lookup_effect_quals env effect_lid)
in (FStar_List.contains FStar_Syntax_Syntax.Reifiable quals)))


let is_reifiable : env  ->  FStar_Syntax_Syntax.residual_comp  ->  Prims.bool = (fun env c -> (is_reifiable_effect env c.FStar_Syntax_Syntax.residual_effect))


let is_reifiable_comp : env  ->  FStar_Syntax_Syntax.comp  ->  Prims.bool = (fun env c -> (match (c.FStar_Syntax_Syntax.n) with
| FStar_Syntax_Syntax.Comp (ct) -> begin
(is_reifiable_effect env ct.FStar_Syntax_Syntax.effect_name)
end
| uu____13536 -> begin
false
end))


let is_reifiable_function : env  ->  FStar_Syntax_Syntax.term  ->  Prims.bool = (fun env t -> (

let uu____13545 = (

let uu____13546 = (FStar_Syntax_Subst.compress t)
in uu____13546.FStar_Syntax_Syntax.n)
in (match (uu____13545) with
| FStar_Syntax_Syntax.Tm_arrow (uu____13549, c) -> begin
(is_reifiable_comp env c)
end
| uu____13567 -> begin
false
end)))


let push_in_gamma : env  ->  binding  ->  env = (fun env s -> (

let rec push1 = (fun x rest -> (match (rest) with
| (Binding_sig (uu____13591))::uu____13592 -> begin
(x)::rest
end
| (Binding_sig_inst (uu____13601))::uu____13602 -> begin
(x)::rest
end
| [] -> begin
(x)::[]
end
| (local)::rest1 -> begin
(

let uu____13617 = (push1 x rest1)
in (local)::uu____13617)
end))
in ((env.tc_hooks.tc_push_in_gamma_hook env s);
(

let uu___155_13621 = env
in (

let uu____13622 = (push1 s env.gamma)
in {solver = uu___155_13621.solver; range = uu___155_13621.range; curmodule = uu___155_13621.curmodule; gamma = uu____13622; gamma_cache = uu___155_13621.gamma_cache; modules = uu___155_13621.modules; expected_typ = uu___155_13621.expected_typ; sigtab = uu___155_13621.sigtab; is_pattern = uu___155_13621.is_pattern; instantiate_imp = uu___155_13621.instantiate_imp; effects = uu___155_13621.effects; generalize = uu___155_13621.generalize; letrecs = uu___155_13621.letrecs; top_level = uu___155_13621.top_level; check_uvars = uu___155_13621.check_uvars; use_eq = uu___155_13621.use_eq; is_iface = uu___155_13621.is_iface; admit = uu___155_13621.admit; lax = uu___155_13621.lax; lax_universes = uu___155_13621.lax_universes; failhard = uu___155_13621.failhard; nosynth = uu___155_13621.nosynth; tc_term = uu___155_13621.tc_term; type_of = uu___155_13621.type_of; universe_of = uu___155_13621.universe_of; use_bv_sorts = uu___155_13621.use_bv_sorts; qname_and_index = uu___155_13621.qname_and_index; proof_ns = uu___155_13621.proof_ns; synth = uu___155_13621.synth; is_native_tactic = uu___155_13621.is_native_tactic; identifier_info = uu___155_13621.identifier_info; tc_hooks = uu___155_13621.tc_hooks; dsenv = uu___155_13621.dsenv}));
)))


let push_sigelt : env  ->  FStar_Syntax_Syntax.sigelt  ->  env = (fun env s -> (

let env1 = (push_in_gamma env (Binding_sig ((((FStar_Syntax_Util.lids_of_sigelt s)), (s)))))
in (build_lattice env1 s)))


let push_sigelt_inst : env  ->  FStar_Syntax_Syntax.sigelt  ->  FStar_Syntax_Syntax.universes  ->  env = (fun env s us -> (

let env1 = (push_in_gamma env (Binding_sig_inst ((((FStar_Syntax_Util.lids_of_sigelt s)), (s), (us)))))
in (build_lattice env1 s)))


let push_local_binding : env  ->  binding  ->  env = (fun env b -> (

let uu___156_13659 = env
in {solver = uu___156_13659.solver; range = uu___156_13659.range; curmodule = uu___156_13659.curmodule; gamma = (b)::env.gamma; gamma_cache = uu___156_13659.gamma_cache; modules = uu___156_13659.modules; expected_typ = uu___156_13659.expected_typ; sigtab = uu___156_13659.sigtab; is_pattern = uu___156_13659.is_pattern; instantiate_imp = uu___156_13659.instantiate_imp; effects = uu___156_13659.effects; generalize = uu___156_13659.generalize; letrecs = uu___156_13659.letrecs; top_level = uu___156_13659.top_level; check_uvars = uu___156_13659.check_uvars; use_eq = uu___156_13659.use_eq; is_iface = uu___156_13659.is_iface; admit = uu___156_13659.admit; lax = uu___156_13659.lax; lax_universes = uu___156_13659.lax_universes; failhard = uu___156_13659.failhard; nosynth = uu___156_13659.nosynth; tc_term = uu___156_13659.tc_term; type_of = uu___156_13659.type_of; universe_of = uu___156_13659.universe_of; use_bv_sorts = uu___156_13659.use_bv_sorts; qname_and_index = uu___156_13659.qname_and_index; proof_ns = uu___156_13659.proof_ns; synth = uu___156_13659.synth; is_native_tactic = uu___156_13659.is_native_tactic; identifier_info = uu___156_13659.identifier_info; tc_hooks = uu___156_13659.tc_hooks; dsenv = uu___156_13659.dsenv}))


let push_bv : env  ->  FStar_Syntax_Syntax.bv  ->  env = (fun env x -> (push_local_binding env (Binding_var (x))))


let pop_bv : env  ->  (FStar_Syntax_Syntax.bv * env) FStar_Pervasives_Native.option = (fun env -> (match (env.gamma) with
| (Binding_var (x))::rest -> begin
FStar_Pervasives_Native.Some (((x), ((

let uu___157_13693 = env
in {solver = uu___157_13693.solver; range = uu___157_13693.range; curmodule = uu___157_13693.curmodule; gamma = rest; gamma_cache = uu___157_13693.gamma_cache; modules = uu___157_13693.modules; expected_typ = uu___157_13693.expected_typ; sigtab = uu___157_13693.sigtab; is_pattern = uu___157_13693.is_pattern; instantiate_imp = uu___157_13693.instantiate_imp; effects = uu___157_13693.effects; generalize = uu___157_13693.generalize; letrecs = uu___157_13693.letrecs; top_level = uu___157_13693.top_level; check_uvars = uu___157_13693.check_uvars; use_eq = uu___157_13693.use_eq; is_iface = uu___157_13693.is_iface; admit = uu___157_13693.admit; lax = uu___157_13693.lax; lax_universes = uu___157_13693.lax_universes; failhard = uu___157_13693.failhard; nosynth = uu___157_13693.nosynth; tc_term = uu___157_13693.tc_term; type_of = uu___157_13693.type_of; universe_of = uu___157_13693.universe_of; use_bv_sorts = uu___157_13693.use_bv_sorts; qname_and_index = uu___157_13693.qname_and_index; proof_ns = uu___157_13693.proof_ns; synth = uu___157_13693.synth; is_native_tactic = uu___157_13693.is_native_tactic; identifier_info = uu___157_13693.identifier_info; tc_hooks = uu___157_13693.tc_hooks; dsenv = uu___157_13693.dsenv}))))
end
| uu____13694 -> begin
FStar_Pervasives_Native.None
end))


let push_binders : env  ->  FStar_Syntax_Syntax.binders  ->  env = (fun env bs -> (FStar_List.fold_left (fun env1 uu____13718 -> (match (uu____13718) with
| (x, uu____13724) -> begin
(push_bv env1 x)
end)) env bs))


let binding_of_lb : FStar_Syntax_Syntax.lbname  ->  (FStar_Syntax_Syntax.univ_name Prims.list * FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)  ->  binding = (fun x t -> (match (x) with
| FStar_Util.Inl (x1) -> begin
(

let x2 = (

let uu___158_13754 = x1
in {FStar_Syntax_Syntax.ppname = uu___158_13754.FStar_Syntax_Syntax.ppname; FStar_Syntax_Syntax.index = uu___158_13754.FStar_Syntax_Syntax.index; FStar_Syntax_Syntax.sort = (FStar_Pervasives_Native.snd t)})
in Binding_var (x2))
end
| FStar_Util.Inr (fv) -> begin
Binding_lid (((fv.FStar_Syntax_Syntax.fv_name.FStar_Syntax_Syntax.v), (t)))
end))


let push_let_binding : env  ->  FStar_Syntax_Syntax.lbname  ->  FStar_Syntax_Syntax.tscheme  ->  env = (fun env lb ts -> (push_local_binding env (binding_of_lb lb ts)))


let push_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (fun env m -> ((add_sigelts env m.FStar_Syntax_Syntax.exports);
(

let uu___159_13789 = env
in {solver = uu___159_13789.solver; range = uu___159_13789.range; curmodule = uu___159_13789.curmodule; gamma = []; gamma_cache = uu___159_13789.gamma_cache; modules = (m)::env.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___159_13789.sigtab; is_pattern = uu___159_13789.is_pattern; instantiate_imp = uu___159_13789.instantiate_imp; effects = uu___159_13789.effects; generalize = uu___159_13789.generalize; letrecs = uu___159_13789.letrecs; top_level = uu___159_13789.top_level; check_uvars = uu___159_13789.check_uvars; use_eq = uu___159_13789.use_eq; is_iface = uu___159_13789.is_iface; admit = uu___159_13789.admit; lax = uu___159_13789.lax; lax_universes = uu___159_13789.lax_universes; failhard = uu___159_13789.failhard; nosynth = uu___159_13789.nosynth; tc_term = uu___159_13789.tc_term; type_of = uu___159_13789.type_of; universe_of = uu___159_13789.universe_of; use_bv_sorts = uu___159_13789.use_bv_sorts; qname_and_index = uu___159_13789.qname_and_index; proof_ns = uu___159_13789.proof_ns; synth = uu___159_13789.synth; is_native_tactic = uu___159_13789.is_native_tactic; identifier_info = uu___159_13789.identifier_info; tc_hooks = uu___159_13789.tc_hooks; dsenv = uu___159_13789.dsenv});
))


let push_univ_vars : env  ->  FStar_Syntax_Syntax.univ_names  ->  env = (fun env xs -> (FStar_List.fold_left (fun env1 x -> (push_local_binding env1 (Binding_univ (x)))) env xs))


let open_universes_in : env  ->  FStar_Syntax_Syntax.univ_names  ->  FStar_Syntax_Syntax.term Prims.list  ->  (env * FStar_Syntax_Syntax.univ_names * FStar_Syntax_Syntax.term Prims.list) = (fun env uvs terms -> (

let uu____13826 = (FStar_Syntax_Subst.univ_var_opening uvs)
in (match (uu____13826) with
| (univ_subst, univ_vars) -> begin
(

let env' = (push_univ_vars env univ_vars)
in (

let uu____13854 = (FStar_List.map (FStar_Syntax_Subst.subst univ_subst) terms)
in ((env'), (univ_vars), (uu____13854))))
end)))


let set_expected_typ : env  ->  FStar_Syntax_Syntax.typ  ->  env = (fun env t -> (

let uu___160_13869 = env
in {solver = uu___160_13869.solver; range = uu___160_13869.range; curmodule = uu___160_13869.curmodule; gamma = uu___160_13869.gamma; gamma_cache = uu___160_13869.gamma_cache; modules = uu___160_13869.modules; expected_typ = FStar_Pervasives_Native.Some (t); sigtab = uu___160_13869.sigtab; is_pattern = uu___160_13869.is_pattern; instantiate_imp = uu___160_13869.instantiate_imp; effects = uu___160_13869.effects; generalize = uu___160_13869.generalize; letrecs = uu___160_13869.letrecs; top_level = uu___160_13869.top_level; check_uvars = uu___160_13869.check_uvars; use_eq = false; is_iface = uu___160_13869.is_iface; admit = uu___160_13869.admit; lax = uu___160_13869.lax; lax_universes = uu___160_13869.lax_universes; failhard = uu___160_13869.failhard; nosynth = uu___160_13869.nosynth; tc_term = uu___160_13869.tc_term; type_of = uu___160_13869.type_of; universe_of = uu___160_13869.universe_of; use_bv_sorts = uu___160_13869.use_bv_sorts; qname_and_index = uu___160_13869.qname_and_index; proof_ns = uu___160_13869.proof_ns; synth = uu___160_13869.synth; is_native_tactic = uu___160_13869.is_native_tactic; identifier_info = uu___160_13869.identifier_info; tc_hooks = uu___160_13869.tc_hooks; dsenv = uu___160_13869.dsenv}))


let expected_typ : env  ->  FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option = (fun env -> (match (env.expected_typ) with
| FStar_Pervasives_Native.None -> begin
FStar_Pervasives_Native.None
end
| FStar_Pervasives_Native.Some (t) -> begin
FStar_Pervasives_Native.Some (t)
end))


let clear_expected_typ : env  ->  (env * FStar_Syntax_Syntax.typ FStar_Pervasives_Native.option) = (fun env_ -> (

let uu____13895 = (expected_typ env_)
in (((

let uu___161_13901 = env_
in {solver = uu___161_13901.solver; range = uu___161_13901.range; curmodule = uu___161_13901.curmodule; gamma = uu___161_13901.gamma; gamma_cache = uu___161_13901.gamma_cache; modules = uu___161_13901.modules; expected_typ = FStar_Pervasives_Native.None; sigtab = uu___161_13901.sigtab; is_pattern = uu___161_13901.is_pattern; instantiate_imp = uu___161_13901.instantiate_imp; effects = uu___161_13901.effects; generalize = uu___161_13901.generalize; letrecs = uu___161_13901.letrecs; top_level = uu___161_13901.top_level; check_uvars = uu___161_13901.check_uvars; use_eq = false; is_iface = uu___161_13901.is_iface; admit = uu___161_13901.admit; lax = uu___161_13901.lax; lax_universes = uu___161_13901.lax_universes; failhard = uu___161_13901.failhard; nosynth = uu___161_13901.nosynth; tc_term = uu___161_13901.tc_term; type_of = uu___161_13901.type_of; universe_of = uu___161_13901.universe_of; use_bv_sorts = uu___161_13901.use_bv_sorts; qname_and_index = uu___161_13901.qname_and_index; proof_ns = uu___161_13901.proof_ns; synth = uu___161_13901.synth; is_native_tactic = uu___161_13901.is_native_tactic; identifier_info = uu___161_13901.identifier_info; tc_hooks = uu___161_13901.tc_hooks; dsenv = uu___161_13901.dsenv})), (uu____13895))))


let finish_module : env  ->  FStar_Syntax_Syntax.modul  ->  env = (

let empty_lid = (FStar_Ident.lid_of_ids (((FStar_Ident.id_of_text ""))::[]))
in (fun env m -> (

let sigs = (match ((FStar_Ident.lid_equals m.FStar_Syntax_Syntax.name FStar_Parser_Const.prims_lid)) with
| true -> begin
(

let uu____13916 = (FStar_All.pipe_right env.gamma (FStar_List.collect (fun uu___138_13926 -> (match (uu___138_13926) with
| Binding_sig (uu____13929, se) -> begin
(se)::[]
end
| uu____13935 -> begin
[]
end))))
in (FStar_All.pipe_right uu____13916 FStar_List.rev))
end
| uu____13940 -> begin
m.FStar_Syntax_Syntax.exports
end)
in ((add_sigelts env sigs);
(

let uu___162_13942 = env
in {solver = uu___162_13942.solver; range = uu___162_13942.range; curmodule = empty_lid; gamma = []; gamma_cache = uu___162_13942.gamma_cache; modules = (m)::env.modules; expected_typ = uu___162_13942.expected_typ; sigtab = uu___162_13942.sigtab; is_pattern = uu___162_13942.is_pattern; instantiate_imp = uu___162_13942.instantiate_imp; effects = uu___162_13942.effects; generalize = uu___162_13942.generalize; letrecs = uu___162_13942.letrecs; top_level = uu___162_13942.top_level; check_uvars = uu___162_13942.check_uvars; use_eq = uu___162_13942.use_eq; is_iface = uu___162_13942.is_iface; admit = uu___162_13942.admit; lax = uu___162_13942.lax; lax_universes = uu___162_13942.lax_universes; failhard = uu___162_13942.failhard; nosynth = uu___162_13942.nosynth; tc_term = uu___162_13942.tc_term; type_of = uu___162_13942.type_of; universe_of = uu___162_13942.universe_of; use_bv_sorts = uu___162_13942.use_bv_sorts; qname_and_index = uu___162_13942.qname_and_index; proof_ns = uu___162_13942.proof_ns; synth = uu___162_13942.synth; is_native_tactic = uu___162_13942.is_native_tactic; identifier_info = uu___162_13942.identifier_info; tc_hooks = uu___162_13942.tc_hooks; dsenv = uu___162_13942.dsenv});
))))


let uvars_in_env : env  ->  FStar_Syntax_Syntax.uvars = (fun env -> (

let no_uvs = (FStar_Syntax_Free.new_uv_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_univ (uu____14024))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____14028, (uu____14029, t)))::tl1 -> begin
(

let uu____14044 = (

let uu____14051 = (FStar_Syntax_Free.uvars t)
in (ext out uu____14051))
in (aux uu____14044 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____14058; FStar_Syntax_Syntax.index = uu____14059; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____14066 = (

let uu____14073 = (FStar_Syntax_Free.uvars t)
in (ext out uu____14073))
in (aux uu____14066 tl1))
end
| (Binding_sig (uu____14080))::uu____14081 -> begin
out
end
| (Binding_sig_inst (uu____14090))::uu____14091 -> begin
out
end))
in (aux no_uvs env.gamma)))))


let univ_vars : env  ->  FStar_Syntax_Syntax.universe_uvar FStar_Util.set = (fun env -> (

let no_univs = (FStar_Syntax_Free.new_universe_uvar_set ())
in (

let ext = (fun out uvs -> (FStar_Util.set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (uu____14147))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uu____14159))::tl1 -> begin
(aux out tl1)
end
| (Binding_lid (uu____14163, (uu____14164, t)))::tl1 -> begin
(

let uu____14179 = (

let uu____14182 = (FStar_Syntax_Free.univs t)
in (ext out uu____14182))
in (aux uu____14179 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____14185; FStar_Syntax_Syntax.index = uu____14186; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____14193 = (

let uu____14196 = (FStar_Syntax_Free.univs t)
in (ext out uu____14196))
in (aux uu____14193 tl1))
end
| (Binding_sig (uu____14199))::uu____14200 -> begin
out
end))
in (aux no_univs env.gamma)))))


let univnames : env  ->  FStar_Syntax_Syntax.univ_name FStar_Util.fifo_set = (fun env -> (

let no_univ_names = FStar_Syntax_Syntax.no_universe_names
in (

let ext = (fun out uvs -> (FStar_Util.fifo_set_union out uvs))
in (

let rec aux = (fun out g -> (match (g) with
| [] -> begin
out
end
| (Binding_sig_inst (uu____14254))::tl1 -> begin
(aux out tl1)
end
| (Binding_univ (uname))::tl1 -> begin
(

let uu____14270 = (FStar_Util.fifo_set_add uname out)
in (aux uu____14270 tl1))
end
| (Binding_lid (uu____14273, (uu____14274, t)))::tl1 -> begin
(

let uu____14289 = (

let uu____14292 = (FStar_Syntax_Free.univnames t)
in (ext out uu____14292))
in (aux uu____14289 tl1))
end
| (Binding_var ({FStar_Syntax_Syntax.ppname = uu____14295; FStar_Syntax_Syntax.index = uu____14296; FStar_Syntax_Syntax.sort = t}))::tl1 -> begin
(

let uu____14303 = (

let uu____14306 = (FStar_Syntax_Free.univnames t)
in (ext out uu____14306))
in (aux uu____14303 tl1))
end
| (Binding_sig (uu____14309))::uu____14310 -> begin
out
end))
in (aux no_univ_names env.gamma)))))


let bound_vars_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.bv Prims.list = (fun bs -> (FStar_All.pipe_right bs (FStar_List.collect (fun uu___139_14335 -> (match (uu___139_14335) with
| Binding_var (x) -> begin
(x)::[]
end
| Binding_lid (uu____14339) -> begin
[]
end
| Binding_sig (uu____14344) -> begin
[]
end
| Binding_univ (uu____14351) -> begin
[]
end
| Binding_sig_inst (uu____14352) -> begin
[]
end)))))


let binders_of_bindings : binding Prims.list  ->  FStar_Syntax_Syntax.binders = (fun bs -> (

let uu____14369 = (

let uu____14372 = (bound_vars_of_bindings bs)
in (FStar_All.pipe_right uu____14372 (FStar_List.map FStar_Syntax_Syntax.mk_binder)))
in (FStar_All.pipe_right uu____14369 FStar_List.rev)))


let bound_vars : env  ->  FStar_Syntax_Syntax.bv Prims.list = (fun env -> (bound_vars_of_bindings env.gamma))


let all_binders : env  ->  FStar_Syntax_Syntax.binders = (fun env -> (binders_of_bindings env.gamma))


let print_gamma : env  ->  Prims.unit = (fun env -> (

let uu____14397 = (

let uu____14398 = (FStar_All.pipe_right env.gamma (FStar_List.map (fun uu___140_14408 -> (match (uu___140_14408) with
| Binding_var (x) -> begin
(

let uu____14410 = (FStar_Syntax_Print.bv_to_string x)
in (Prims.strcat "Binding_var " uu____14410))
end
| Binding_univ (u) -> begin
(Prims.strcat "Binding_univ " u.FStar_Ident.idText)
end
| Binding_lid (l, uu____14413) -> begin
(

let uu____14414 = (FStar_Ident.string_of_lid l)
in (Prims.strcat "Binding_lid " uu____14414))
end
| Binding_sig (ls, uu____14416) -> begin
(

let uu____14421 = (

let uu____14422 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____14422 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig " uu____14421))
end
| Binding_sig_inst (ls, uu____14432, uu____14433) -> begin
(

let uu____14438 = (

let uu____14439 = (FStar_All.pipe_right ls (FStar_List.map FStar_Ident.string_of_lid))
in (FStar_All.pipe_right uu____14439 (FStar_String.concat ", ")))
in (Prims.strcat "Binding_sig_inst " uu____14438))
end))))
in (FStar_All.pipe_right uu____14398 (FStar_String.concat "::\n")))
in (FStar_All.pipe_right uu____14397 (FStar_Util.print1 "%s\n"))))


let eq_gamma : env  ->  env  ->  Prims.bool = (fun env env' -> (

let uu____14458 = (FStar_Util.physical_equality env.gamma env'.gamma)
in (match (uu____14458) with
| true -> begin
true
end
| uu____14461 -> begin
(

let g = (all_binders env)
in (

let g' = (all_binders env')
in ((Prims.op_Equality (FStar_List.length g) (FStar_List.length g')) && (FStar_List.forall2 (fun uu____14486 uu____14487 -> (match (((uu____14486), (uu____14487))) with
| ((b1, uu____14505), (b2, uu____14507)) -> begin
(FStar_Syntax_Syntax.bv_eq b1 b2)
end)) g g'))))
end)))


let fold_env : 'a . env  ->  ('a  ->  binding  ->  'a)  ->  'a  ->  'a = (fun env f a -> (FStar_List.fold_right (fun e a1 -> (f a1 e)) env.gamma a))


let string_of_delta_level : delta_level  ->  Prims.string = (fun uu___141_14554 -> (match (uu___141_14554) with
| NoDelta -> begin
"NoDelta"
end
| Inlining -> begin
"Inlining"
end
| Eager_unfolding_only -> begin
"Eager_unfolding_only"
end
| Unfold (uu____14555) -> begin
"Unfold _"
end
| UnfoldTac -> begin
"UnfoldTac"
end))


let lidents : env  ->  FStar_Ident.lident Prims.list = (fun env -> (

let keys = (FStar_List.fold_left (fun keys uu___142_14574 -> (match (uu___142_14574) with
| Binding_sig (lids, uu____14580) -> begin
(FStar_List.append lids keys)
end
| uu____14585 -> begin
keys
end)) [] env.gamma)
in (FStar_Util.smap_fold (sigtab env) (fun uu____14591 v1 keys1 -> (FStar_List.append (FStar_Syntax_Util.lids_of_sigelt v1) keys1)) keys)))


let should_enc_path : env  ->  Prims.string Prims.list  ->  Prims.bool = (fun env path -> (

let rec list_prefix = (fun xs ys -> (match (((xs), (ys))) with
| ([], uu____14627) -> begin
true
end
| ((x)::xs1, (y)::ys1) -> begin
((Prims.op_Equality x y) && (list_prefix xs1 ys1))
end
| (uu____14646, uu____14647) -> begin
false
end))
in (

let rec should_enc_path' = (fun pns path1 -> (match (pns) with
| [] -> begin
true
end
| ((p, b))::pns1 -> begin
(

let uu____14684 = (list_prefix p path1)
in (match (uu____14684) with
| true -> begin
b
end
| uu____14685 -> begin
(should_enc_path' pns1 path1)
end))
end))
in (should_enc_path' (FStar_List.flatten env.proof_ns) path))))


let should_enc_lid : env  ->  FStar_Ident.lident  ->  Prims.bool = (fun env lid -> (

let uu____14698 = (FStar_Ident.path_of_lid lid)
in (should_enc_path env uu____14698)))


let cons_proof_ns : Prims.bool  ->  env  ->  name_prefix  ->  env = (fun b e path -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (pns)::rest -> begin
(

let pns' = (((path), (b)))::pns
in (

let uu___163_14728 = e
in {solver = uu___163_14728.solver; range = uu___163_14728.range; curmodule = uu___163_14728.curmodule; gamma = uu___163_14728.gamma; gamma_cache = uu___163_14728.gamma_cache; modules = uu___163_14728.modules; expected_typ = uu___163_14728.expected_typ; sigtab = uu___163_14728.sigtab; is_pattern = uu___163_14728.is_pattern; instantiate_imp = uu___163_14728.instantiate_imp; effects = uu___163_14728.effects; generalize = uu___163_14728.generalize; letrecs = uu___163_14728.letrecs; top_level = uu___163_14728.top_level; check_uvars = uu___163_14728.check_uvars; use_eq = uu___163_14728.use_eq; is_iface = uu___163_14728.is_iface; admit = uu___163_14728.admit; lax = uu___163_14728.lax; lax_universes = uu___163_14728.lax_universes; failhard = uu___163_14728.failhard; nosynth = uu___163_14728.nosynth; tc_term = uu___163_14728.tc_term; type_of = uu___163_14728.type_of; universe_of = uu___163_14728.universe_of; use_bv_sorts = uu___163_14728.use_bv_sorts; qname_and_index = uu___163_14728.qname_and_index; proof_ns = (pns')::rest; synth = uu___163_14728.synth; is_native_tactic = uu___163_14728.is_native_tactic; identifier_info = uu___163_14728.identifier_info; tc_hooks = uu___163_14728.tc_hooks; dsenv = uu___163_14728.dsenv}))
end))


let add_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns true e path))


let rem_proof_ns : env  ->  name_prefix  ->  env = (fun e path -> (cons_proof_ns false e path))


let push_proof_ns : env  ->  env = (fun e -> (

let uu___164_14755 = e
in {solver = uu___164_14755.solver; range = uu___164_14755.range; curmodule = uu___164_14755.curmodule; gamma = uu___164_14755.gamma; gamma_cache = uu___164_14755.gamma_cache; modules = uu___164_14755.modules; expected_typ = uu___164_14755.expected_typ; sigtab = uu___164_14755.sigtab; is_pattern = uu___164_14755.is_pattern; instantiate_imp = uu___164_14755.instantiate_imp; effects = uu___164_14755.effects; generalize = uu___164_14755.generalize; letrecs = uu___164_14755.letrecs; top_level = uu___164_14755.top_level; check_uvars = uu___164_14755.check_uvars; use_eq = uu___164_14755.use_eq; is_iface = uu___164_14755.is_iface; admit = uu___164_14755.admit; lax = uu___164_14755.lax; lax_universes = uu___164_14755.lax_universes; failhard = uu___164_14755.failhard; nosynth = uu___164_14755.nosynth; tc_term = uu___164_14755.tc_term; type_of = uu___164_14755.type_of; universe_of = uu___164_14755.universe_of; use_bv_sorts = uu___164_14755.use_bv_sorts; qname_and_index = uu___164_14755.qname_and_index; proof_ns = ([])::e.proof_ns; synth = uu___164_14755.synth; is_native_tactic = uu___164_14755.is_native_tactic; identifier_info = uu___164_14755.identifier_info; tc_hooks = uu___164_14755.tc_hooks; dsenv = uu___164_14755.dsenv}))


let pop_proof_ns : env  ->  env = (fun e -> (match (e.proof_ns) with
| [] -> begin
(failwith "empty proof_ns stack!")
end
| (uu____14770)::rest -> begin
(

let uu___165_14774 = e
in {solver = uu___165_14774.solver; range = uu___165_14774.range; curmodule = uu___165_14774.curmodule; gamma = uu___165_14774.gamma; gamma_cache = uu___165_14774.gamma_cache; modules = uu___165_14774.modules; expected_typ = uu___165_14774.expected_typ; sigtab = uu___165_14774.sigtab; is_pattern = uu___165_14774.is_pattern; instantiate_imp = uu___165_14774.instantiate_imp; effects = uu___165_14774.effects; generalize = uu___165_14774.generalize; letrecs = uu___165_14774.letrecs; top_level = uu___165_14774.top_level; check_uvars = uu___165_14774.check_uvars; use_eq = uu___165_14774.use_eq; is_iface = uu___165_14774.is_iface; admit = uu___165_14774.admit; lax = uu___165_14774.lax; lax_universes = uu___165_14774.lax_universes; failhard = uu___165_14774.failhard; nosynth = uu___165_14774.nosynth; tc_term = uu___165_14774.tc_term; type_of = uu___165_14774.type_of; universe_of = uu___165_14774.universe_of; use_bv_sorts = uu___165_14774.use_bv_sorts; qname_and_index = uu___165_14774.qname_and_index; proof_ns = rest; synth = uu___165_14774.synth; is_native_tactic = uu___165_14774.is_native_tactic; identifier_info = uu___165_14774.identifier_info; tc_hooks = uu___165_14774.tc_hooks; dsenv = uu___165_14774.dsenv})
end))


let get_proof_ns : env  ->  proof_namespace = (fun e -> e.proof_ns)


let set_proof_ns : proof_namespace  ->  env  ->  env = (fun ns e -> (

let uu___166_14787 = e
in {solver = uu___166_14787.solver; range = uu___166_14787.range; curmodule = uu___166_14787.curmodule; gamma = uu___166_14787.gamma; gamma_cache = uu___166_14787.gamma_cache; modules = uu___166_14787.modules; expected_typ = uu___166_14787.expected_typ; sigtab = uu___166_14787.sigtab; is_pattern = uu___166_14787.is_pattern; instantiate_imp = uu___166_14787.instantiate_imp; effects = uu___166_14787.effects; generalize = uu___166_14787.generalize; letrecs = uu___166_14787.letrecs; top_level = uu___166_14787.top_level; check_uvars = uu___166_14787.check_uvars; use_eq = uu___166_14787.use_eq; is_iface = uu___166_14787.is_iface; admit = uu___166_14787.admit; lax = uu___166_14787.lax; lax_universes = uu___166_14787.lax_universes; failhard = uu___166_14787.failhard; nosynth = uu___166_14787.nosynth; tc_term = uu___166_14787.tc_term; type_of = uu___166_14787.type_of; universe_of = uu___166_14787.universe_of; use_bv_sorts = uu___166_14787.use_bv_sorts; qname_and_index = uu___166_14787.qname_and_index; proof_ns = ns; synth = uu___166_14787.synth; is_native_tactic = uu___166_14787.is_native_tactic; identifier_info = uu___166_14787.identifier_info; tc_hooks = uu___166_14787.tc_hooks; dsenv = uu___166_14787.dsenv}))


let string_of_proof_ns : env  ->  Prims.string = (fun env -> (

let string_of_proof_ns' = (fun pns -> (

let uu____14816 = (FStar_List.map (fun fpns -> (

let uu____14838 = (

let uu____14839 = (

let uu____14840 = (FStar_List.map (fun uu____14852 -> (match (uu____14852) with
| (p, b) -> begin
(Prims.strcat (match (b) with
| true -> begin
"+"
end
| uu____14865 -> begin
"-"
end) (FStar_String.concat "." p))
end)) fpns)
in (FStar_String.concat "," uu____14840))
in (Prims.strcat uu____14839 "]"))
in (Prims.strcat "[" uu____14838))) pns)
in (FStar_String.concat ";" uu____14816)))
in (string_of_proof_ns' env.proof_ns)))


let dummy_solver : solver_t = {init = (fun uu____14868 -> ()); push = (fun uu____14870 -> ()); pop = (fun uu____14872 -> ()); encode_modul = (fun uu____14875 uu____14876 -> ()); encode_sig = (fun uu____14879 uu____14880 -> ()); preprocess = (fun e g -> (

let uu____14886 = (

let uu____14893 = (FStar_Options.peek ())
in ((e), (g), (uu____14893)))
in (uu____14886)::[])); solve = (fun uu____14909 uu____14910 uu____14911 -> ()); finish = (fun uu____14917 -> ()); refresh = (fun uu____14919 -> ())}




