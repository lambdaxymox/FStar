open Prims
type env_t = FStar_Extraction_ML_UEnv.uenv
let (fail_exp :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax)
  =
  fun lid ->
    fun t ->
      let uu____25 =
        let uu____26 =
          let uu____43 =
            FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          let uu____46 =
            let uu____57 = FStar_Syntax_Syntax.iarg t in
            let uu____66 =
              let uu____77 =
                let uu____86 =
                  let uu____87 =
                    let uu____88 =
                      let uu____89 =
                        let uu____94 =
                          let uu____95 = FStar_Syntax_Print.lid_to_string lid in
                          Prims.op_Hat "Not yet implemented:" uu____95 in
                        (uu____94, FStar_Range.dummyRange) in
                      FStar_Const.Const_string uu____89 in
                    FStar_Syntax_Syntax.Tm_constant uu____88 in
                  FStar_Syntax_Syntax.mk uu____87 FStar_Range.dummyRange in
                FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____86 in
              [uu____77] in
            uu____57 :: uu____66 in
          (uu____43, uu____46) in
        FStar_Syntax_Syntax.Tm_app uu____26 in
      FStar_Syntax_Syntax.mk uu____25 FStar_Range.dummyRange
let (always_fail :
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.letbinding)
  =
  fun lid ->
    fun t ->
      let imp =
        let uu____157 = FStar_Syntax_Util.arrow_formals t in
        match uu____157 with
        | ([], t1) ->
            let b =
              let uu____184 =
                FStar_Syntax_Syntax.gen_bv "_" FStar_Pervasives_Native.None
                  t1 in
              FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder uu____184 in
            let uu____191 = fail_exp lid t1 in
            FStar_Syntax_Util.abs [b] uu____191 FStar_Pervasives_Native.None
        | (bs, t1) ->
            let uu____212 = fail_exp lid t1 in
            FStar_Syntax_Util.abs bs uu____212 FStar_Pervasives_Native.None in
      let lb =
        let uu____216 =
          let uu____221 =
            FStar_Syntax_Syntax.lid_as_fv lid
              FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
          FStar_Util.Inr uu____221 in
        {
          FStar_Syntax_Syntax.lbname = uu____216;
          FStar_Syntax_Syntax.lbunivs = [];
          FStar_Syntax_Syntax.lbtyp = t;
          FStar_Syntax_Syntax.lbeff = FStar_Parser_Const.effect_ML_lid;
          FStar_Syntax_Syntax.lbdef = imp;
          FStar_Syntax_Syntax.lbattrs = [];
          FStar_Syntax_Syntax.lbpos = (imp.FStar_Syntax_Syntax.pos)
        } in
      lb
let as_pair : 'uuuuuu228 . 'uuuuuu228 Prims.list -> ('uuuuuu228 * 'uuuuuu228)
  =
  fun uu___0_239 ->
    match uu___0_239 with
    | a::b::[] -> (a, b)
    | uu____244 -> failwith "Expected a list with 2 elements"
let (flag_of_qual :
  FStar_Syntax_Syntax.qualifier ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun uu___1_257 ->
    match uu___1_257 with
    | FStar_Syntax_Syntax.Assumption ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Assumed
    | FStar_Syntax_Syntax.Private ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | FStar_Syntax_Syntax.NoExtract ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.NoExtract
    | uu____260 -> FStar_Pervasives_Native.None
let rec (extract_meta :
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.meta FStar_Pervasives_Native.option)
  =
  fun x ->
    let uu____268 = FStar_Syntax_Subst.compress x in
    match uu____268 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____272;
        FStar_Syntax_Syntax.vars = uu____273;_} ->
        let uu____276 =
          let uu____277 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____277 in
        (match uu____276 with
         | "FStar.Pervasives.PpxDerivingShow" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingShow
         | "FStar.Pervasives.PpxDerivingYoJson" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.PpxDerivingYoJson
         | "FStar.Pervasives.CInline" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
         | "FStar.Pervasives.Substitute" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.Substitute
         | "FStar.Pervasives.Gc" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
         | "FStar.Pervasives.CAbstractStruct" ->
             FStar_Pervasives_Native.Some
               FStar_Extraction_ML_Syntax.CAbstract
         | "FStar.Pervasives.CIfDef" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CIfDef
         | "FStar.Pervasives.CMacro" ->
             FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CMacro
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated "")
         | uu____280 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____282;
             FStar_Syntax_Syntax.vars = uu____283;_},
           ({
              FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
                (FStar_Const.Const_string (s, uu____285));
              FStar_Syntax_Syntax.pos = uu____286;
              FStar_Syntax_Syntax.vars = uu____287;_},
            uu____288)::[]);
        FStar_Syntax_Syntax.pos = uu____289;
        FStar_Syntax_Syntax.vars = uu____290;_} ->
        let uu____331 =
          let uu____332 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____332 in
        (match uu____331 with
         | "FStar.Pervasives.PpxDerivingShowConstant" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant s)
         | "FStar.Pervasives.Comment" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Comment s)
         | "FStar.Pervasives.CPrologue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CPrologue s)
         | "FStar.Pervasives.CEpilogue" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CEpilogue s)
         | "FStar.Pervasives.CConst" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CConst s)
         | "FStar.Pervasives.CCConv" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.CCConv s)
         | "Prims.deprecated" ->
             FStar_Pervasives_Native.Some
               (FStar_Extraction_ML_Syntax.Deprecated s)
         | uu____335 -> FStar_Pervasives_Native.None)
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("KremlinPrivate", uu____336));
        FStar_Syntax_Syntax.pos = uu____337;
        FStar_Syntax_Syntax.vars = uu____338;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Private
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("c_inline", uu____341));
        FStar_Syntax_Syntax.pos = uu____342;
        FStar_Syntax_Syntax.vars = uu____343;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_constant
          (FStar_Const.Const_string ("substitute", uu____346));
        FStar_Syntax_Syntax.pos = uu____347;
        FStar_Syntax_Syntax.vars = uu____348;_} ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1, uu____352);
        FStar_Syntax_Syntax.pos = uu____353;
        FStar_Syntax_Syntax.vars = uu____354;_} -> extract_meta x1
    | uu____361 ->
        let uu____362 = FStar_Syntax_Util.head_and_args x in
        (match uu____362 with
         | (head, args) ->
             let uu____407 =
               let uu____422 =
                 let uu____423 = FStar_Syntax_Subst.compress head in
                 uu____423.FStar_Syntax_Syntax.n in
               (uu____422, args) in
             (match uu____407 with
              | (FStar_Syntax_Syntax.Tm_fvar fv, uu____439::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.remove_unused_type_parameters_lid
                  ->
                  let uu____474 =
                    let uu____479 =
                      FStar_ToSyntax_ToSyntax.parse_attr_with_list false x
                        FStar_Parser_Const.remove_unused_type_parameters_lid in
                    FStar_Pervasives_Native.fst uu____479 in
                  (match uu____474 with
                   | FStar_Pervasives_Native.None ->
                       FStar_Pervasives_Native.None
                   | FStar_Pervasives_Native.Some l ->
                       let uu____501 =
                         let uu____502 =
                           let uu____509 = FStar_Syntax_Syntax.range_of_fv fv in
                           (l, uu____509) in
                         FStar_Extraction_ML_Syntax.RemoveUnusedTypeParameters
                           uu____502 in
                       FStar_Pervasives_Native.Some uu____501)
              | uu____512 -> FStar_Pervasives_Native.None))
let (extract_metadata :
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.meta Prims.list)
  = fun metas -> FStar_List.choose extract_meta metas
let binders_as_mlty_binders :
  'uuuuuu544 .
    FStar_Extraction_ML_UEnv.uenv ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu544) Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlident
          Prims.list)
  =
  fun env ->
    fun bs ->
      FStar_Util.fold_map
        (fun env1 ->
           fun uu____584 ->
             match uu____584 with
             | (bv, uu____594) ->
                 let env2 = FStar_Extraction_ML_UEnv.extend_ty env1 bv false in
                 let name =
                   let uu____597 = FStar_Extraction_ML_UEnv.lookup_bv env2 bv in
                   match uu____597 with
                   | FStar_Util.Inl ty ->
                       ty.FStar_Extraction_ML_UEnv.ty_b_name
                   | uu____599 -> failwith "Impossible" in
                 (env2, name)) env bs
type data_constructor =
  {
  dname: FStar_Ident.lident ;
  dtyp: FStar_Syntax_Syntax.typ }
let (__proj__Mkdata_constructor__item__dname :
  data_constructor -> FStar_Ident.lident) =
  fun projectee -> match projectee with | { dname; dtyp;_} -> dname
let (__proj__Mkdata_constructor__item__dtyp :
  data_constructor -> FStar_Syntax_Syntax.typ) =
  fun projectee -> match projectee with | { dname; dtyp;_} -> dtyp
type inductive_family =
  {
  ifv: FStar_Syntax_Syntax.fv ;
  iname: FStar_Ident.lident ;
  iparams: FStar_Syntax_Syntax.binders ;
  ityp: FStar_Syntax_Syntax.term ;
  idatas: data_constructor Prims.list ;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list ;
  imetadata: FStar_Extraction_ML_Syntax.metadata }
let (__proj__Mkinductive_family__item__ifv :
  inductive_family -> FStar_Syntax_Syntax.fv) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ifv
let (__proj__Mkinductive_family__item__iname :
  inductive_family -> FStar_Ident.lident) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iname
let (__proj__Mkinductive_family__item__iparams :
  inductive_family -> FStar_Syntax_Syntax.binders) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iparams
let (__proj__Mkinductive_family__item__ityp :
  inductive_family -> FStar_Syntax_Syntax.term) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> ityp
let (__proj__Mkinductive_family__item__idatas :
  inductive_family -> data_constructor Prims.list) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> idatas
let (__proj__Mkinductive_family__item__iquals :
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> iquals
let (__proj__Mkinductive_family__item__imetadata :
  inductive_family -> FStar_Extraction_ML_Syntax.metadata) =
  fun projectee ->
    match projectee with
    | { ifv; iname; iparams; ityp; idatas; iquals; imetadata;_} -> imetadata
let (print_ifamily : inductive_family -> unit) =
  fun i ->
    let uu____788 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____789 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____790 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____791 =
      let uu____792 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d ->
                let uu____803 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____804 =
                  let uu____805 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.op_Hat " : " uu____805 in
                Prims.op_Hat uu____803 uu____804)) in
      FStar_All.pipe_right uu____792 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____788 uu____789 uu____790
      uu____791
let (bundle_as_inductive_families :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * inductive_family Prims.list))
  =
  fun env ->
    fun ses ->
      fun quals ->
        let uu____843 =
          FStar_Util.fold_map
            (fun env1 ->
               fun se ->
                 match se.FStar_Syntax_Syntax.sigel with
                 | FStar_Syntax_Syntax.Sig_inductive_typ
                     (l, us, bs, t, _mut_i, datas) ->
                     let uu____896 = FStar_Syntax_Subst.open_univ_vars us t in
                     (match uu____896 with
                      | (_us, t1) ->
                          let uu____909 = FStar_Syntax_Subst.open_term bs t1 in
                          (match uu____909 with
                           | (bs1, t2) ->
                               let datas1 =
                                 FStar_All.pipe_right ses
                                   (FStar_List.collect
                                      (fun se1 ->
                                         match se1.FStar_Syntax_Syntax.sigel
                                         with
                                         | FStar_Syntax_Syntax.Sig_datacon
                                             (d, us1, t3, l', nparams,
                                              uu____955)
                                             when FStar_Ident.lid_equals l l'
                                             ->
                                             let uu____960 =
                                               FStar_Syntax_Subst.open_univ_vars
                                                 us1 t3 in
                                             (match uu____960 with
                                              | (_us1, t4) ->
                                                  let uu____969 =
                                                    FStar_Syntax_Util.arrow_formals
                                                      t4 in
                                                  (match uu____969 with
                                                   | (bs', body) ->
                                                       let uu____984 =
                                                         FStar_Util.first_N
                                                           (FStar_List.length
                                                              bs1) bs' in
                                                       (match uu____984 with
                                                        | (bs_params, rest)
                                                            ->
                                                            let subst =
                                                              FStar_List.map2
                                                                (fun
                                                                   uu____1075
                                                                   ->
                                                                   fun
                                                                    uu____1076
                                                                    ->
                                                                    match 
                                                                    (uu____1075,
                                                                    uu____1076)
                                                                    with
                                                                    | 
                                                                    ((b',
                                                                    uu____1102),
                                                                    (b,
                                                                    uu____1104))
                                                                    ->
                                                                    let uu____1125
                                                                    =
                                                                    let uu____1132
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                    (b',
                                                                    uu____1132) in
                                                                    FStar_Syntax_Syntax.NT
                                                                    uu____1125)
                                                                bs_params bs1 in
                                                            let t5 =
                                                              let uu____1138
                                                                =
                                                                let uu____1139
                                                                  =
                                                                  FStar_Syntax_Syntax.mk_Total
                                                                    body in
                                                                FStar_Syntax_Util.arrow
                                                                  rest
                                                                  uu____1139 in
                                                              FStar_All.pipe_right
                                                                uu____1138
                                                                (FStar_Syntax_Subst.subst
                                                                   subst) in
                                                            [{
                                                               dname = d;
                                                               dtyp = t5
                                                             }])))
                                         | uu____1142 -> [])) in
                               let metadata =
                                 let uu____1146 =
                                   extract_metadata
                                     se.FStar_Syntax_Syntax.sigattrs in
                                 let uu____1149 =
                                   FStar_List.choose flag_of_qual quals in
                                 FStar_List.append uu____1146 uu____1149 in
                               let fv =
                                 FStar_Syntax_Syntax.lid_as_fv l
                                   FStar_Syntax_Syntax.delta_constant
                                   FStar_Pervasives_Native.None in
                               let uu____1153 =
                                 FStar_Extraction_ML_UEnv.extend_type_name
                                   env1 fv in
                               (match uu____1153 with
                                | (uu____1164, env2) ->
                                    (env2,
                                      [{
                                         ifv = fv;
                                         iname = l;
                                         iparams = bs1;
                                         ityp = t2;
                                         idatas = datas1;
                                         iquals =
                                           (se.FStar_Syntax_Syntax.sigquals);
                                         imetadata = metadata
                                       }]))))
                 | uu____1168 -> (env1, [])) env ses in
        match uu____843 with
        | (env1, ifams) -> (env1, (FStar_List.flatten ifams))
type tydef_declaration =
  (FStar_Extraction_ML_Syntax.mlsymbol * FStar_Extraction_ML_Syntax.metadata
    * Prims.int)
type iface =
  {
  iface_module_name: FStar_Extraction_ML_Syntax.mlpath ;
  iface_bindings:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list
    ;
  iface_tydefs:
    (FStar_Extraction_ML_UEnv.tydef, tydef_declaration) FStar_Util.either
      Prims.list
    ;
  iface_type_names:
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list }
let (__proj__Mkiface__item__iface_module_name :
  iface -> FStar_Extraction_ML_Syntax.mlpath) =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_module_name
let (__proj__Mkiface__item__iface_bindings :
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding)
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_bindings
let (__proj__Mkiface__item__iface_tydefs :
  iface ->
    (FStar_Extraction_ML_UEnv.tydef, tydef_declaration) FStar_Util.either
      Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_tydefs
let (__proj__Mkiface__item__iface_type_names :
  iface ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list)
  =
  fun projectee ->
    match projectee with
    | { iface_module_name; iface_bindings; iface_tydefs; iface_type_names;_}
        -> iface_type_names
let (empty_iface : iface) =
  {
    iface_module_name = ([], "");
    iface_bindings = [];
    iface_tydefs = [];
    iface_type_names = []
  }
let (iface_of_bindings :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) Prims.list
    -> iface)
  =
  fun fvs ->
    let uu___234_1408 = empty_iface in
    {
      iface_module_name = (uu___234_1408.iface_module_name);
      iface_bindings = fvs;
      iface_tydefs = (uu___234_1408.iface_tydefs);
      iface_type_names = (uu___234_1408.iface_type_names)
    }
let (iface_of_tydefs : FStar_Extraction_ML_UEnv.tydef Prims.list -> iface) =
  fun tds ->
    let uu___237_1418 = empty_iface in
    let uu____1419 =
      FStar_List.map (fun uu____1430 -> FStar_Util.Inl uu____1430) tds in
    let uu____1431 =
      FStar_List.map
        (fun td ->
           let uu____1446 = FStar_Extraction_ML_UEnv.tydef_fv td in
           let uu____1447 = FStar_Extraction_ML_UEnv.tydef_mlpath td in
           (uu____1446, uu____1447)) tds in
    {
      iface_module_name = (uu___237_1418.iface_module_name);
      iface_bindings = (uu___237_1418.iface_bindings);
      iface_tydefs = uu____1419;
      iface_type_names = uu____1431
    }
let (iface_of_type_names :
  (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_Syntax.mlpath) Prims.list ->
    iface)
  =
  fun fvs ->
    let uu___241_1465 = empty_iface in
    {
      iface_module_name = (uu___241_1465.iface_module_name);
      iface_bindings = (uu___241_1465.iface_bindings);
      iface_tydefs = (uu___241_1465.iface_tydefs);
      iface_type_names = fvs
    }
let (iface_union : iface -> iface -> iface) =
  fun if1 ->
    fun if2 ->
      let uu____1476 =
        if if1.iface_module_name <> if1.iface_module_name
        then failwith "Union not defined"
        else if1.iface_module_name in
      {
        iface_module_name = uu____1476;
        iface_bindings =
          (FStar_List.append if1.iface_bindings if2.iface_bindings);
        iface_tydefs = (FStar_List.append if1.iface_tydefs if2.iface_tydefs);
        iface_type_names =
          (FStar_List.append if1.iface_type_names if2.iface_type_names)
      }
let (iface_union_l : iface Prims.list -> iface) =
  fun ifs -> FStar_List.fold_right iface_union ifs empty_iface
let (mlpath_to_string : FStar_Extraction_ML_Syntax.mlpath -> Prims.string) =
  fun p ->
    FStar_String.concat ". "
      (FStar_List.append (FStar_Pervasives_Native.fst p)
         [FStar_Pervasives_Native.snd p])
let tscheme_to_string :
  'uuuuuu1514 .
    FStar_Extraction_ML_Syntax.mlpath ->
      ('uuuuuu1514 * FStar_Extraction_ML_Syntax.mlty) -> Prims.string
  =
  fun cm ->
    fun ts ->
      FStar_Extraction_ML_Code.string_of_mlty cm
        (FStar_Pervasives_Native.snd ts)
let (print_exp_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    FStar_Extraction_ML_UEnv.exp_binding -> Prims.string)
  =
  fun cm ->
    fun e ->
      let uu____1543 =
        FStar_Extraction_ML_Code.string_of_mlexpr cm
          e.FStar_Extraction_ML_UEnv.exp_b_expr in
      let uu____1544 =
        tscheme_to_string cm e.FStar_Extraction_ML_UEnv.exp_b_tscheme in
      FStar_Util.format3
        "{\n\texp_b_name = %s\n\texp_b_expr = %s\n\texp_b_tscheme = %s }"
        e.FStar_Extraction_ML_UEnv.exp_b_name uu____1543 uu____1544
let (print_binding :
  FStar_Extraction_ML_Syntax.mlpath ->
    (FStar_Syntax_Syntax.fv * FStar_Extraction_ML_UEnv.exp_binding) ->
      Prims.string)
  =
  fun cm ->
    fun uu____1558 ->
      match uu____1558 with
      | (fv, exp_binding) ->
          let uu____1565 = FStar_Syntax_Print.fv_to_string fv in
          let uu____1566 = print_exp_binding cm exp_binding in
          FStar_Util.format2 "(%s, %s)" uu____1565 uu____1566
let print_tydef :
  'uuuuuu1575 'uuuuuu1576 .
    FStar_Extraction_ML_Syntax.mlpath ->
      (FStar_Extraction_ML_UEnv.tydef,
        (Prims.string * 'uuuuuu1575 * 'uuuuuu1576)) FStar_Util.either ->
        Prims.string
  =
  fun cm ->
    fun tydef ->
      let uu____1607 =
        match tydef with
        | FStar_Util.Inl tydef1 ->
            let uu____1623 =
              let uu____1624 = FStar_Extraction_ML_UEnv.tydef_fv tydef1 in
              FStar_Syntax_Print.fv_to_string uu____1624 in
            let uu____1625 =
              let uu____1626 = FStar_Extraction_ML_UEnv.tydef_def tydef1 in
              tscheme_to_string cm uu____1626 in
            (uu____1623, uu____1625)
        | FStar_Util.Inr (p, uu____1632, uu____1633) -> (p, "None") in
      match uu____1607 with
      | (name, defn) -> FStar_Util.format2 "(%s, %s)" name defn
let (iface_to_string : iface -> Prims.string) =
  fun iface1 ->
    let cm = iface1.iface_module_name in
    let print_type_name uu____1657 =
      match uu____1657 with
      | (tn, uu____1663) -> FStar_Syntax_Print.fv_to_string tn in
    let uu____1664 =
      let uu____1665 =
        FStar_List.map (print_binding cm) iface1.iface_bindings in
      FStar_All.pipe_right uu____1665 (FStar_String.concat "\n") in
    let uu____1674 =
      let uu____1675 = FStar_List.map (print_tydef cm) iface1.iface_tydefs in
      FStar_All.pipe_right uu____1675 (FStar_String.concat "\n") in
    let uu____1684 =
      let uu____1685 = FStar_List.map print_type_name iface1.iface_type_names in
      FStar_All.pipe_right uu____1685 (FStar_String.concat "\n") in
    FStar_Util.format4
      "Interface %s = {\niface_bindings=\n%s;\n\niface_tydefs=\n%s;\n\niface_type_names=%s;\n}"
      (mlpath_to_string iface1.iface_module_name) uu____1664 uu____1674
      uu____1684
let (gamma_to_string : FStar_Extraction_ML_UEnv.uenv -> Prims.string) =
  fun env ->
    let cm = FStar_Extraction_ML_UEnv.current_module_of_uenv env in
    let gamma =
      let uu____1707 = FStar_Extraction_ML_UEnv.bindings_of_uenv env in
      FStar_List.collect
        (fun uu___2_1717 ->
           match uu___2_1717 with
           | FStar_Extraction_ML_UEnv.Fv (b, e) -> [(b, e)]
           | uu____1734 -> []) uu____1707 in
    let uu____1739 =
      let uu____1740 = FStar_List.map (print_binding cm) gamma in
      FStar_All.pipe_right uu____1740 (FStar_String.concat "\n") in
    FStar_Util.format1 "Gamma = {\n %s }" uu____1739
let (extract_typ_abbrev :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun quals ->
      fun attrs ->
        fun lb ->
          let uu____1793 =
            let uu____1802 =
              let uu____1811 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
              FStar_TypeChecker_Env.open_universes_in uu____1811
                lb.FStar_Syntax_Syntax.lbunivs
                [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
            match uu____1802 with
            | (tcenv, uu____1821, def_typ) ->
                let uu____1827 = as_pair def_typ in (tcenv, uu____1827) in
          match uu____1793 with
          | (tcenv, (lbdef, lbtyp)) ->
              let lbtyp1 =
                FStar_TypeChecker_Normalize.normalize
                  [FStar_TypeChecker_Env.Beta;
                  FStar_TypeChecker_Env.UnfoldUntil
                    FStar_Syntax_Syntax.delta_constant;
                  FStar_TypeChecker_Env.ForExtraction] tcenv lbtyp in
              let lbdef1 =
                FStar_TypeChecker_Normalize.eta_expand_with_type tcenv lbdef
                  lbtyp1 in
              let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
              let def =
                let uu____1858 =
                  let uu____1859 = FStar_Syntax_Subst.compress lbdef1 in
                  FStar_All.pipe_right uu____1859 FStar_Syntax_Util.unmeta in
                FStar_All.pipe_right uu____1858 FStar_Syntax_Util.un_uinst in
              let def1 =
                match def.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs uu____1867 ->
                    FStar_Extraction_ML_Term.normalize_abs def
                | uu____1886 -> def in
              let uu____1887 =
                match def1.FStar_Syntax_Syntax.n with
                | FStar_Syntax_Syntax.Tm_abs (bs, body, uu____1898) ->
                    FStar_Syntax_Subst.open_term bs body
                | uu____1923 -> ([], def1) in
              (match uu____1887 with
               | (bs, body) ->
                   let assumed =
                     FStar_Util.for_some
                       (fun uu___3_1942 ->
                          match uu___3_1942 with
                          | FStar_Syntax_Syntax.Assumption -> true
                          | uu____1943 -> false) quals in
                   let uu____1944 = binders_as_mlty_binders env bs in
                   (match uu____1944 with
                    | (env1, ml_bs) ->
                        let body1 =
                          let uu____1968 =
                            FStar_Extraction_ML_Term.term_as_mlty env1 body in
                          FStar_All.pipe_right uu____1968
                            (FStar_Extraction_ML_Util.eraseTypeDeep
                               (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                        let metadata =
                          let has_val_decl =
                            FStar_Extraction_ML_UEnv.has_tydef_declaration
                              env lid in
                          let meta =
                            let uu____1974 = extract_metadata attrs in
                            let uu____1977 =
                              FStar_List.choose flag_of_qual quals in
                            FStar_List.append uu____1974 uu____1977 in
                          if has_val_decl
                          then
                            let uu____1980 =
                              let uu____1981 = FStar_Ident.range_of_lid lid in
                              FStar_Extraction_ML_Syntax.HasValDecl
                                uu____1981 in
                            uu____1980 :: meta
                          else meta in
                        let tyscheme = (ml_bs, body1) in
                        let uu____1988 =
                          let uu____2001 =
                            FStar_All.pipe_right quals
                              (FStar_Util.for_some
                                 (fun uu___4_2005 ->
                                    match uu___4_2005 with
                                    | FStar_Syntax_Syntax.Assumption -> true
                                    | FStar_Syntax_Syntax.New -> true
                                    | uu____2006 -> false)) in
                          if uu____2001
                          then
                            let uu____2019 =
                              FStar_Extraction_ML_UEnv.extend_type_name env
                                fv in
                            match uu____2019 with
                            | (mlp, env2) ->
                                (mlp, (iface_of_type_names [(fv, mlp)]),
                                  env2)
                          else
                            (let uu____2053 =
                               FStar_Extraction_ML_UEnv.extend_tydef env fv
                                 tyscheme metadata in
                             match uu____2053 with
                             | (td, mlp, env2) ->
                                 let uu____2075 = iface_of_tydefs [td] in
                                 (mlp, uu____2075, env2)) in
                        (match uu____1988 with
                         | (mlpath, iface1, env2) ->
                             let td =
                               {
                                 FStar_Extraction_ML_Syntax.tydecl_assumed =
                                   assumed;
                                 FStar_Extraction_ML_Syntax.tydecl_name =
                                   (FStar_Pervasives_Native.snd mlpath);
                                 FStar_Extraction_ML_Syntax.tydecl_ignored =
                                   FStar_Pervasives_Native.None;
                                 FStar_Extraction_ML_Syntax.tydecl_parameters
                                   = ml_bs;
                                 FStar_Extraction_ML_Syntax.tydecl_meta =
                                   metadata;
                                 FStar_Extraction_ML_Syntax.tydecl_defn =
                                   (FStar_Pervasives_Native.Some
                                      (FStar_Extraction_ML_Syntax.MLTD_Abbrev
                                         body1))
                               } in
                             let def2 =
                               let uu____2111 =
                                 let uu____2112 =
                                   let uu____2113 =
                                     FStar_Ident.range_of_lid lid in
                                   FStar_Extraction_ML_Util.mlloc_of_range
                                     uu____2113 in
                                 FStar_Extraction_ML_Syntax.MLM_Loc
                                   uu____2112 in
                               [uu____2111;
                               FStar_Extraction_ML_Syntax.MLM_Ty [td]] in
                             (env2, iface1, def2))))
let (extract_let_rec_type :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.qualifier Prims.list ->
      FStar_Syntax_Syntax.term Prims.list ->
        FStar_Syntax_Syntax.letbinding ->
          (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun env ->
    fun quals ->
      fun attrs ->
        fun lb ->
          let lbtyp =
            let uu____2161 = FStar_Extraction_ML_UEnv.tcenv_of_uenv env in
            FStar_TypeChecker_Normalize.normalize
              [FStar_TypeChecker_Env.Beta;
              FStar_TypeChecker_Env.AllowUnboundUniverses;
              FStar_TypeChecker_Env.EraseUniverses;
              FStar_TypeChecker_Env.UnfoldUntil
                FStar_Syntax_Syntax.delta_constant;
              FStar_TypeChecker_Env.ForExtraction] uu____2161
              lb.FStar_Syntax_Syntax.lbtyp in
          let uu____2162 = FStar_Syntax_Util.arrow_formals lbtyp in
          match uu____2162 with
          | (bs, uu____2178) ->
              let uu____2183 = binders_as_mlty_binders env bs in
              (match uu____2183 with
               | (env1, ml_bs) ->
                   let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                   let lid =
                     (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   let body = FStar_Extraction_ML_Syntax.MLTY_Top in
                   let metadata =
                     let uu____2212 = extract_metadata attrs in
                     let uu____2215 = FStar_List.choose flag_of_qual quals in
                     FStar_List.append uu____2212 uu____2215 in
                   let assumed = false in
                   let tscheme = (ml_bs, body) in
                   let uu____2224 =
                     FStar_Extraction_ML_UEnv.extend_tydef env fv tscheme
                       metadata in
                   (match uu____2224 with
                    | (tydef, mlp, env2) ->
                        let td =
                          {
                            FStar_Extraction_ML_Syntax.tydecl_assumed =
                              assumed;
                            FStar_Extraction_ML_Syntax.tydecl_name =
                              (FStar_Pervasives_Native.snd mlp);
                            FStar_Extraction_ML_Syntax.tydecl_ignored =
                              FStar_Pervasives_Native.None;
                            FStar_Extraction_ML_Syntax.tydecl_parameters =
                              ml_bs;
                            FStar_Extraction_ML_Syntax.tydecl_meta = metadata;
                            FStar_Extraction_ML_Syntax.tydecl_defn =
                              (FStar_Pervasives_Native.Some
                                 (FStar_Extraction_ML_Syntax.MLTD_Abbrev body))
                          } in
                        let def =
                          let uu____2248 =
                            let uu____2249 =
                              let uu____2250 = FStar_Ident.range_of_lid lid in
                              FStar_Extraction_ML_Util.mlloc_of_range
                                uu____2250 in
                            FStar_Extraction_ML_Syntax.MLM_Loc uu____2249 in
                          [uu____2248;
                          FStar_Extraction_ML_Syntax.MLM_Ty [td]] in
                        let iface1 = iface_of_tydefs [tydef] in
                        (env2, iface1, def)))
let (extract_bundle_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (env_t * iface))
  =
  fun env ->
    fun se ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____2314 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____2314 in
        let tys = (ml_tyvars, mlt) in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____2321 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false in
        match uu____2321 with | (env2, uu____2337, b) -> (env2, (fvv, b)) in
      let extract_one_family env1 ind =
        let uu____2374 = binders_as_mlty_binders env1 ind.iparams in
        match uu____2374 with
        | (env_iparams, vars) ->
            let uu____2399 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1) in
            (match uu____2399 with
             | (env2, ctors) ->
                 let env3 =
                   let uu____2451 =
                     FStar_Util.find_opt
                       (fun uu___5_2456 ->
                          match uu___5_2456 with
                          | FStar_Syntax_Syntax.RecordType uu____2457 -> true
                          | uu____2466 -> false) ind.iquals in
                   match uu____2451 with
                   | FStar_Pervasives_Native.Some
                       (FStar_Syntax_Syntax.RecordType (ns, ids)) ->
                       let g =
                         FStar_List.fold_right
                           (fun id ->
                              fun g ->
                                let uu____2485 =
                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                    g ((ind.iname), id) in
                                match uu____2485 with
                                | (uu____2490, g1) -> g1) ids env2 in
                       g
                   | uu____2492 -> env2 in
                 (env3, ctors)) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu____2508, t, uu____2510, uu____2511, uu____2512);
            FStar_Syntax_Syntax.sigrng = uu____2513;
            FStar_Syntax_Syntax.sigquals = uu____2514;
            FStar_Syntax_Syntax.sigmeta = uu____2515;
            FStar_Syntax_Syntax.sigattrs = uu____2516;
            FStar_Syntax_Syntax.sigopts = uu____2517;_}::[],
          uu____2518),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu____2537 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu____2537 with
           | (env1, ctor) -> (env1, (iface_of_bindings [ctor])))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu____2569), quals) ->
          let uu____2583 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr in
          if uu____2583
          then (env, empty_iface)
          else
            (let uu____2589 = bundle_as_inductive_families env ses quals in
             match uu____2589 with
             | (env1, ifams) ->
                 let uu____2606 =
                   FStar_Util.fold_map extract_one_family env1 ifams in
                 (match uu____2606 with
                  | (env2, td) ->
                      let uu____2647 =
                        let uu____2648 =
                          let uu____2649 =
                            FStar_List.map
                              (fun x ->
                                 let uu____2663 =
                                   FStar_Extraction_ML_UEnv.mlpath_of_lident
                                     env2 x.iname in
                                 ((x.ifv), uu____2663)) ifams in
                          iface_of_type_names uu____2649 in
                        iface_union uu____2648
                          (iface_of_bindings (FStar_List.flatten td)) in
                      (env2, uu____2647)))
      | uu____2668 -> failwith "Unexpected signature element"
let (extract_type_declaration :
  FStar_Extraction_ML_UEnv.uenv ->
    Prims.bool ->
      FStar_Ident.lident ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          FStar_Syntax_Syntax.term Prims.list ->
            FStar_Syntax_Syntax.univ_name Prims.list ->
              FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
                (env_t * iface * FStar_Extraction_ML_Syntax.mlmodule1
                  Prims.list))
  =
  fun g ->
    fun is_interface_val ->
      fun lid ->
        fun quals ->
          fun attrs ->
            fun univs ->
              fun t ->
                let uu____2746 =
                  let uu____2747 =
                    FStar_All.pipe_right quals
                      (FStar_Util.for_some
                         (fun uu___6_2751 ->
                            match uu___6_2751 with
                            | FStar_Syntax_Syntax.Assumption -> true
                            | uu____2752 -> false)) in
                  Prims.op_Negation uu____2747 in
                if uu____2746
                then
                  let g1 =
                    FStar_Extraction_ML_UEnv.extend_with_tydef_declaration g
                      lid in
                  (g1, empty_iface, [])
                else
                  (let uu____2765 = FStar_Syntax_Util.arrow_formals t in
                   match uu____2765 with
                   | (bs, uu____2781) ->
                       let fv =
                         FStar_Syntax_Syntax.lid_as_fv lid
                           FStar_Syntax_Syntax.delta_constant
                           FStar_Pervasives_Native.None in
                       let lb =
                         let uu____2788 =
                           FStar_Syntax_Util.abs bs
                             FStar_Syntax_Syntax.t_unit
                             FStar_Pervasives_Native.None in
                         {
                           FStar_Syntax_Syntax.lbname = (FStar_Util.Inr fv);
                           FStar_Syntax_Syntax.lbunivs = univs;
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_Tot_lid;
                           FStar_Syntax_Syntax.lbdef = uu____2788;
                           FStar_Syntax_Syntax.lbattrs = attrs;
                           FStar_Syntax_Syntax.lbpos =
                             (t.FStar_Syntax_Syntax.pos)
                         } in
                       let uu____2791 = extract_typ_abbrev g quals attrs lb in
                       (match uu____2791 with
                        | (g1, iface1, mods) ->
                            let iface2 =
                              if is_interface_val
                              then
                                let mlp =
                                  FStar_Extraction_ML_UEnv.mlpath_of_lident
                                    g1 lid in
                                let meta = extract_metadata attrs in
                                let uu___472_2820 = empty_iface in
                                {
                                  iface_module_name =
                                    (uu___472_2820.iface_module_name);
                                  iface_bindings =
                                    (uu___472_2820.iface_bindings);
                                  iface_tydefs =
                                    [FStar_Util.Inr
                                       ((FStar_Pervasives_Native.snd mlp),
                                         meta, (FStar_List.length bs))];
                                  iface_type_names =
                                    (uu___472_2820.iface_type_names)
                                }
                              else iface1 in
                            (g1, iface2, mods)))
let (extract_reifiable_effect :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.eff_decl ->
      (FStar_Extraction_ML_UEnv.uenv * iface *
        FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun ed ->
      let extend_iface lid mlp exp exp_binding =
        let fv =
          FStar_Syntax_Syntax.lid_as_fv lid
            FStar_Syntax_Syntax.delta_equational FStar_Pervasives_Native.None in
        let lb =
          {
            FStar_Extraction_ML_Syntax.mllb_name =
              (FStar_Pervasives_Native.snd mlp);
            FStar_Extraction_ML_Syntax.mllb_tysc =
              FStar_Pervasives_Native.None;
            FStar_Extraction_ML_Syntax.mllb_add_unit = false;
            FStar_Extraction_ML_Syntax.mllb_def = exp;
            FStar_Extraction_ML_Syntax.mllb_meta = [];
            FStar_Extraction_ML_Syntax.print_typ = false
          } in
        ((iface_of_bindings [(fv, exp_binding)]),
          (FStar_Extraction_ML_Syntax.MLM_Let
             (FStar_Extraction_ML_Syntax.NonRec, [lb]))) in
      let rec extract_fv tm =
        (let uu____2932 =
           let uu____2933 =
             let uu____2938 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
             FStar_TypeChecker_Env.debug uu____2938 in
           FStar_All.pipe_left uu____2933
             (FStar_Options.Other "ExtractionReify") in
         if uu____2932
         then
           let uu____2939 = FStar_Syntax_Print.term_to_string tm in
           FStar_Util.print1 "extract_fv term: %s\n" uu____2939
         else ());
        (let uu____2941 =
           let uu____2942 = FStar_Syntax_Subst.compress tm in
           uu____2942.FStar_Syntax_Syntax.n in
         match uu____2941 with
         | FStar_Syntax_Syntax.Tm_uinst (tm1, uu____2950) -> extract_fv tm1
         | FStar_Syntax_Syntax.Tm_fvar fv ->
             let mlp =
               FStar_Extraction_ML_UEnv.mlpath_of_lident g
                 (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
             let uu____2957 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
             (match uu____2957 with
              | { FStar_Extraction_ML_UEnv.exp_b_name = uu____2962;
                  FStar_Extraction_ML_UEnv.exp_b_expr = uu____2963;
                  FStar_Extraction_ML_UEnv.exp_b_tscheme = tysc;_} ->
                  let uu____2965 =
                    FStar_All.pipe_left
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top)
                      (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                  (uu____2965, tysc))
         | uu____2966 ->
             let uu____2967 =
               let uu____2968 =
                 FStar_Range.string_of_range tm.FStar_Syntax_Syntax.pos in
               let uu____2969 = FStar_Syntax_Print.term_to_string tm in
               FStar_Util.format2 "(%s) Not an fv: %s" uu____2968 uu____2969 in
             failwith uu____2967) in
      let extract_action g1 a =
        (let uu____2995 =
           let uu____2996 =
             let uu____3001 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
             FStar_TypeChecker_Env.debug uu____3001 in
           FStar_All.pipe_left uu____2996
             (FStar_Options.Other "ExtractionReify") in
         if uu____2995
         then
           let uu____3002 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_typ in
           let uu____3003 =
             FStar_Syntax_Print.term_to_string
               a.FStar_Syntax_Syntax.action_defn in
           FStar_Util.print2 "Action type %s and term %s\n" uu____3002
             uu____3003
         else ());
        (let lbname =
           let uu____3010 =
             FStar_Syntax_Syntax.new_bv
               (FStar_Pervasives_Native.Some
                  ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
               FStar_Syntax_Syntax.tun in
           FStar_Util.Inl uu____3010 in
         let lb =
           FStar_Syntax_Syntax.mk_lb
             (lbname, (a.FStar_Syntax_Syntax.action_univs),
               FStar_Parser_Const.effect_Tot_lid,
               (a.FStar_Syntax_Syntax.action_typ),
               (a.FStar_Syntax_Syntax.action_defn), [],
               ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos)) in
         let lbs = (false, [lb]) in
         let action_lb =
           FStar_Syntax_Syntax.mk
             (FStar_Syntax_Syntax.Tm_let
                (lbs, FStar_Syntax_Util.exp_false_bool))
             (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
         let uu____3036 =
           FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
         match uu____3036 with
         | (a_let, uu____3052, ty) ->
             let uu____3054 =
               match a_let.FStar_Extraction_ML_Syntax.expr with
               | FStar_Extraction_ML_Syntax.MLE_Let
                   ((uu____3071, mllb::[]), uu____3073) ->
                   (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc with
                    | FStar_Pervasives_Native.Some tysc ->
                        ((mllb.FStar_Extraction_ML_Syntax.mllb_def), tysc)
                    | FStar_Pervasives_Native.None ->
                        failwith "No type scheme")
               | uu____3103 -> failwith "Impossible" in
             (match uu____3054 with
              | (exp, tysc) ->
                  let uu____3130 =
                    FStar_Extraction_ML_UEnv.extend_with_action_name g1 ed a
                      tysc in
                  (match uu____3130 with
                   | (a_nm, a_lid, exp_b, g2) ->
                       ((let uu____3152 =
                           let uu____3153 =
                             let uu____3158 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2 in
                             FStar_TypeChecker_Env.debug uu____3158 in
                           FStar_All.pipe_left uu____3153
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____3152
                         then
                           let uu____3159 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____3159
                         else ());
                        (let uu____3162 =
                           let uu____3163 =
                             let uu____3168 =
                               FStar_Extraction_ML_UEnv.tcenv_of_uenv g2 in
                             FStar_TypeChecker_Env.debug uu____3168 in
                           FStar_All.pipe_left uu____3163
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____3162
                         then
                           ((let uu____3170 =
                               FStar_Extraction_ML_Code.string_of_mlty a_nm
                                 (FStar_Pervasives_Native.snd tysc) in
                             FStar_Util.print1 "Extracted action type: %s\n"
                               uu____3170);
                            FStar_List.iter
                              (fun x ->
                                 FStar_Util.print1 "and binders: %s\n" x)
                              (FStar_Pervasives_Native.fst tysc))
                         else ());
                        (let uu____3174 = extend_iface a_lid a_nm exp exp_b in
                         match uu____3174 with
                         | (iface1, impl) -> (g2, (iface1, impl))))))) in
      let uu____3193 =
        let uu____3200 =
          let uu____3205 =
            let uu____3208 =
              let uu____3217 =
                FStar_All.pipe_right ed FStar_Syntax_Util.get_return_repr in
              FStar_All.pipe_right uu____3217 FStar_Util.must in
            FStar_All.pipe_right uu____3208 FStar_Pervasives_Native.snd in
          extract_fv uu____3205 in
        match uu____3200 with
        | (return_tm, ty_sc) ->
            let uu____3286 =
              FStar_Extraction_ML_UEnv.extend_with_monad_op_name g ed
                "return" ty_sc in
            (match uu____3286 with
             | (return_nm, return_lid, return_b, g1) ->
                 let uu____3305 =
                   extend_iface return_lid return_nm return_tm return_b in
                 (match uu____3305 with
                  | (iface1, impl) -> (g1, iface1, impl))) in
      match uu____3193 with
      | (g1, return_iface, return_decl) ->
          let uu____3329 =
            let uu____3336 =
              let uu____3341 =
                let uu____3344 =
                  let uu____3353 =
                    FStar_All.pipe_right ed FStar_Syntax_Util.get_bind_repr in
                  FStar_All.pipe_right uu____3353 FStar_Util.must in
                FStar_All.pipe_right uu____3344 FStar_Pervasives_Native.snd in
              extract_fv uu____3341 in
            match uu____3336 with
            | (bind_tm, ty_sc) ->
                let uu____3422 =
                  FStar_Extraction_ML_UEnv.extend_with_monad_op_name g1 ed
                    "bind" ty_sc in
                (match uu____3422 with
                 | (bind_nm, bind_lid, bind_b, g2) ->
                     let uu____3441 =
                       extend_iface bind_lid bind_nm bind_tm bind_b in
                     (match uu____3441 with
                      | (iface1, impl) -> (g2, iface1, impl))) in
          (match uu____3329 with
           | (g2, bind_iface, bind_decl) ->
               let uu____3465 =
                 FStar_Util.fold_map extract_action g2
                   ed.FStar_Syntax_Syntax.actions in
               (match uu____3465 with
                | (g3, actions) ->
                    let uu____3502 = FStar_List.unzip actions in
                    (match uu____3502 with
                     | (actions_iface, actions1) ->
                         let uu____3529 =
                           iface_union_l (return_iface :: bind_iface ::
                             actions_iface) in
                         (g3, uu____3529, (return_decl :: bind_decl ::
                           actions1)))))
let (extract_let_rec_types :
  FStar_Syntax_Syntax.sigelt ->
    FStar_Extraction_ML_UEnv.uenv ->
      FStar_Syntax_Syntax.letbinding Prims.list ->
        (FStar_Extraction_ML_UEnv.uenv * iface *
          FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun se ->
    fun env ->
      fun lbs ->
        let uu____3559 =
          FStar_Util.for_some
            (fun lb ->
               let uu____3563 =
                 FStar_Extraction_ML_Term.is_arity env
                   lb.FStar_Syntax_Syntax.lbtyp in
               Prims.op_Negation uu____3563) lbs in
        if uu____3559
        then
          FStar_Errors.raise_error
            (FStar_Errors.Fatal_ExtractionUnsupported,
              "Mutually recursively defined typed and terms cannot yet be extracted")
            se.FStar_Syntax_Syntax.sigrng
        else
          (let uu____3581 =
             FStar_List.fold_left
               (fun uu____3616 ->
                  fun lb ->
                    match uu____3616 with
                    | (env1, iface_opt, impls) ->
                        let uu____3657 =
                          extract_let_rec_type env1
                            se.FStar_Syntax_Syntax.sigquals
                            se.FStar_Syntax_Syntax.sigattrs lb in
                        (match uu____3657 with
                         | (env2, iface1, impl) ->
                             let iface_opt1 =
                               match iface_opt with
                               | FStar_Pervasives_Native.None ->
                                   FStar_Pervasives_Native.Some iface1
                               | FStar_Pervasives_Native.Some iface' ->
                                   let uu____3691 = iface_union iface' iface1 in
                                   FStar_Pervasives_Native.Some uu____3691 in
                             (env2, iface_opt1, (impl :: impls))))
               (env, FStar_Pervasives_Native.None, []) lbs in
           match uu____3581 with
           | (env1, iface_opt, impls) ->
               let uu____3731 = FStar_Option.get iface_opt in
               let uu____3732 =
                 FStar_All.pipe_right (FStar_List.rev impls)
                   FStar_List.flatten in
               (env1, uu____3731, uu____3732))
let (extract_sigelt_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun se ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_bundle uu____3763 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_inductive_typ uu____3772 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_datacon uu____3789 ->
          extract_bundle_iface g se
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t) when
          FStar_Extraction_ML_Term.is_arity g t ->
          let uu____3807 =
            extract_type_declaration g true lid
              se.FStar_Syntax_Syntax.sigquals se.FStar_Syntax_Syntax.sigattrs
              univs t in
          (match uu____3807 with | (env, iface1, uu____3822) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____3828) when
          FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp ->
          let uu____3835 =
            extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
              se.FStar_Syntax_Syntax.sigattrs lb in
          (match uu____3835 with | (env, iface1, uu____3850) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_let ((true, lbs), uu____3856) when
          FStar_Util.for_some
            (fun lb ->
               FStar_Extraction_ML_Term.is_arity g
                 lb.FStar_Syntax_Syntax.lbtyp) lbs
          ->
          let uu____3867 = extract_let_rec_types se g lbs in
          (match uu____3867 with | (env, iface1, uu____3882) -> (env, iface1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid, _univs, t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____3893 =
            (FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption))
              &&
              (let uu____3897 =
                 let uu____3898 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                 FStar_TypeChecker_Util.must_erase_for_extraction uu____3898
                   t in
               Prims.op_Negation uu____3897) in
          if uu____3893
          then
            let uu____3903 =
              let uu____3914 =
                let uu____3915 =
                  let uu____3918 = always_fail lid t in [uu____3918] in
                (false, uu____3915) in
              FStar_Extraction_ML_Term.extract_lb_iface g uu____3914 in
            (match uu____3903 with
             | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
          else (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_let (lbs, uu____3941) ->
          let uu____3946 = FStar_Extraction_ML_Term.extract_lb_iface g lbs in
          (match uu____3946 with
           | (g1, bindings) -> (g1, (iface_of_bindings bindings)))
      | FStar_Syntax_Syntax.Sig_assume uu____3975 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____3982 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3983 -> (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____3996 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____4007 ->
          (g, empty_iface)
      | FStar_Syntax_Syntax.Sig_pragma p ->
          (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
           (g, empty_iface))
      | FStar_Syntax_Syntax.Sig_splice uu____4018 ->
          failwith "impossible: trying to extract splice"
      | FStar_Syntax_Syntax.Sig_fail uu____4029 ->
          failwith "impossible: trying to extract Sig_fail"
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____4045 =
            (let uu____4048 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
             FStar_TypeChecker_Env.is_reifiable_effect uu____4048
               ed.FStar_Syntax_Syntax.mname)
              && (FStar_List.isEmpty ed.FStar_Syntax_Syntax.binders) in
          if uu____4045
          then
            let uu____4059 = extract_reifiable_effect g ed in
            (match uu____4059 with
             | (env, iface1, uu____4074) -> (env, iface1))
          else (g, empty_iface)
let (extract_iface' :
  env_t ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu____4094 = FStar_Options.interactive () in
      if uu____4094
      then (g, empty_iface)
      else
        (let uu____4100 = FStar_Options.restore_cmd_line_options true in
         let decls = modul.FStar_Syntax_Syntax.declarations in
         let iface1 =
           let uu___687_4103 = empty_iface in
           let uu____4104 = FStar_Extraction_ML_UEnv.current_module_of_uenv g in
           {
             iface_module_name = uu____4104;
             iface_bindings = (uu___687_4103.iface_bindings);
             iface_tydefs = (uu___687_4103.iface_tydefs);
             iface_type_names = (uu___687_4103.iface_type_names)
           } in
         let res =
           FStar_List.fold_left
             (fun uu____4122 ->
                fun se ->
                  match uu____4122 with
                  | (g1, iface2) ->
                      let uu____4134 = extract_sigelt_iface g1 se in
                      (match uu____4134 with
                       | (g2, iface') ->
                           let uu____4145 = iface_union iface2 iface' in
                           (g2, uu____4145))) (g, iface1) decls in
         (let uu____4147 = FStar_Options.restore_cmd_line_options true in
          FStar_All.pipe_left (fun uu____4148 -> ()) uu____4147);
         res)
let (extract_iface :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul -> (FStar_Extraction_ML_UEnv.uenv * iface))
  =
  fun g ->
    fun modul ->
      let uu____4163 =
        FStar_Syntax_Unionfind.with_uf_enabled
          (fun uu____4175 ->
             let uu____4176 = FStar_Options.debug_any () in
             if uu____4176
             then
               let uu____4181 =
                 let uu____4182 =
                   FStar_Ident.string_of_lid modul.FStar_Syntax_Syntax.name in
                 FStar_Util.format1 "Extracted interface of %s" uu____4182 in
               FStar_Util.measure_execution_time uu____4181
                 (fun uu____4188 -> extract_iface' g modul)
             else extract_iface' g modul) in
      match uu____4163 with
      | (g1, iface1) ->
          let uu____4196 =
            FStar_Extraction_ML_UEnv.with_typars_env g1
              (fun e ->
                 let iface_tydefs =
                   FStar_List.map
                     (fun uu___7_4240 ->
                        match uu___7_4240 with
                        | FStar_Util.Inl td ->
                            let uu____4268 =
                              let uu____4269 =
                                FStar_Extraction_ML_UEnv.tydef_mlpath td in
                              FStar_Pervasives_Native.snd uu____4269 in
                            let uu____4278 =
                              FStar_Extraction_ML_UEnv.tydef_meta td in
                            let uu____4279 =
                              let uu____4284 =
                                FStar_Extraction_ML_UEnv.tydef_def td in
                              FStar_Util.Inl uu____4284 in
                            (uu____4268, uu____4278, uu____4279)
                        | FStar_Util.Inr (p, m, n) ->
                            (p, m, (FStar_Util.Inr n))) iface1.iface_tydefs in
                 let uu____4302 =
                   FStar_Extraction_ML_UEnv.extend_with_module_name g1
                     modul.FStar_Syntax_Syntax.name in
                 match uu____4302 with
                 | (module_name, uu____4314) ->
                     let e1 =
                       FStar_Extraction_ML_RemoveUnusedParameters.set_current_module
                         e module_name in
                     FStar_Extraction_ML_RemoveUnusedParameters.elim_tydefs
                       e1 iface_tydefs) in
          (match uu____4196 with
           | (g2, uu____4321) ->
               let uu____4326 = FStar_Extraction_ML_UEnv.exit_module g2 in
               (uu____4326, iface1))
let (extract_bundle :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mlmodule1
        Prims.list))
  =
  fun env ->
    fun se ->
      let extract_ctor env_iparams ml_tyvars env1 ctor =
        let mlt =
          let uu____4397 =
            FStar_Extraction_ML_Term.term_as_mlty env_iparams ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env_iparams) uu____4397 in
        let steps =
          [FStar_TypeChecker_Env.Inlining;
          FStar_TypeChecker_Env.UnfoldUntil
            FStar_Syntax_Syntax.delta_constant;
          FStar_TypeChecker_Env.EraseUniverses;
          FStar_TypeChecker_Env.AllowUnboundUniverses;
          FStar_TypeChecker_Env.ForExtraction] in
        let names =
          let uu____4404 =
            let uu____4405 =
              let uu____4408 =
                let uu____4409 =
                  FStar_Extraction_ML_UEnv.tcenv_of_uenv env_iparams in
                FStar_TypeChecker_Normalize.normalize steps uu____4409
                  ctor.dtyp in
              FStar_Syntax_Subst.compress uu____4408 in
            uu____4405.FStar_Syntax_Syntax.n in
          match uu____4404 with
          | FStar_Syntax_Syntax.Tm_arrow (bs, uu____4413) ->
              FStar_List.map
                (fun uu____4445 ->
                   match uu____4445 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____4453;
                        FStar_Syntax_Syntax.sort = uu____4454;_},
                      uu____4455) -> FStar_Ident.string_of_id ppname) bs
          | uu____4462 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv =
          FStar_Syntax_Syntax.lid_as_fv ctor.dname
            FStar_Syntax_Syntax.delta_constant FStar_Pervasives_Native.None in
        let uu____4469 =
          FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false in
        match uu____4469 with
        | (env2, mls, uu____4492) ->
            let uu____4493 =
              let uu____4504 =
                let uu____4511 = FStar_Extraction_ML_Util.argTypes mlt in
                FStar_List.zip names uu____4511 in
              (mls, uu____4504) in
            (env2, uu____4493) in
      let extract_one_family env1 ind =
        let uu____4545 = binders_as_mlty_binders env1 ind.iparams in
        match uu____4545 with
        | (env_iparams, vars) ->
            let uu____4564 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor env_iparams vars) env1) in
            (match uu____4564 with
             | (env2, ctors) ->
                 let uu____4639 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____4639 with
                  | (indices, uu____4651) ->
                      let ml_params =
                        let uu____4659 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i ->
                                  fun uu____4682 ->
                                    let uu____4689 =
                                      FStar_Util.string_of_int i in
                                    Prims.op_Hat "'dummyV" uu____4689)) in
                        FStar_List.append vars uu____4659 in
                      let uu____4690 =
                        let uu____4697 =
                          FStar_Util.find_opt
                            (fun uu___8_4702 ->
                               match uu___8_4702 with
                               | FStar_Syntax_Syntax.RecordType uu____4703 ->
                                   true
                               | uu____4712 -> false) ind.iquals in
                        match uu____4697 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns, ids)) ->
                            let uu____4729 = FStar_List.hd ctors in
                            (match uu____4729 with
                             | (uu____4756, c_ty) ->
                                 let uu____4771 =
                                   FStar_List.fold_right2
                                     (fun id ->
                                        fun uu____4807 ->
                                          fun uu____4808 ->
                                            match (uu____4807, uu____4808)
                                            with
                                            | ((uu____4847, ty), (fields, g))
                                                ->
                                                let uu____4877 =
                                                  FStar_Extraction_ML_UEnv.extend_record_field_name
                                                    g ((ind.iname), id) in
                                                (match uu____4877 with
                                                 | (mlid, g1) ->
                                                     (((mlid, ty) :: fields),
                                                       g1))) ids c_ty
                                     ([], env2) in
                                 (match uu____4771 with
                                  | (fields, g) ->
                                      ((FStar_Pervasives_Native.Some
                                          (FStar_Extraction_ML_Syntax.MLTD_Record
                                             fields)), g)))
                        | uu____4936 when
                            (FStar_List.length ctors) = Prims.int_zero ->
                            (FStar_Pervasives_Native.None, env2)
                        | uu____4951 ->
                            ((FStar_Pervasives_Native.Some
                                (FStar_Extraction_ML_Syntax.MLTD_DType ctors)),
                              env2) in
                      (match uu____4690 with
                       | (tbody, env3) ->
                           let td =
                             let uu____4967 =
                               let uu____4968 =
                                 FStar_Extraction_ML_UEnv.mlpath_of_lident
                                   env3 ind.iname in
                               FStar_Pervasives_Native.snd uu____4968 in
                             {
                               FStar_Extraction_ML_Syntax.tydecl_assumed =
                                 false;
                               FStar_Extraction_ML_Syntax.tydecl_name =
                                 uu____4967;
                               FStar_Extraction_ML_Syntax.tydecl_ignored =
                                 FStar_Pervasives_Native.None;
                               FStar_Extraction_ML_Syntax.tydecl_parameters =
                                 ml_params;
                               FStar_Extraction_ML_Syntax.tydecl_meta =
                                 (ind.imetadata);
                               FStar_Extraction_ML_Syntax.tydecl_defn = tbody
                             } in
                           (env3, td)))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l, uu____4986, t, uu____4988, uu____4989, uu____4990);
            FStar_Syntax_Syntax.sigrng = uu____4991;
            FStar_Syntax_Syntax.sigquals = uu____4992;
            FStar_Syntax_Syntax.sigmeta = uu____4993;
            FStar_Syntax_Syntax.sigattrs = uu____4994;
            FStar_Syntax_Syntax.sigopts = uu____4995;_}::[],
          uu____4996),
         (FStar_Syntax_Syntax.ExceptionConstructor)::[]) ->
          let uu____5015 = extract_ctor env [] env { dname = l; dtyp = t } in
          (match uu____5015 with
           | (env1, ctor) ->
               (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses, uu____5061), quals) ->
          let uu____5075 =
            FStar_Syntax_Util.has_attribute se.FStar_Syntax_Syntax.sigattrs
              FStar_Parser_Const.erasable_attr in
          if uu____5075
          then (env, [])
          else
            (let uu____5085 = bundle_as_inductive_families env ses quals in
             match uu____5085 with
             | (env1, ifams) ->
                 let uu____5104 =
                   FStar_Util.fold_map extract_one_family env1 ifams in
                 (match uu____5104 with
                  | (env2, td) ->
                      (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____5125 -> failwith "Unexpected signature element"
let (maybe_register_plugin :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
  =
  fun g ->
    fun se ->
      let w =
        FStar_Extraction_ML_Syntax.with_ty
          FStar_Extraction_ML_Syntax.MLTY_Top in
      let plugin_with_arity attrs =
        FStar_Util.find_map attrs
          (fun t ->
             let uu____5179 = FStar_Syntax_Util.head_and_args t in
             match uu____5179 with
             | (head, args) ->
                 let uu____5226 =
                   let uu____5227 =
                     FStar_Syntax_Util.is_fvar FStar_Parser_Const.plugin_attr
                       head in
                   Prims.op_Negation uu____5227 in
                 if uu____5226
                 then FStar_Pervasives_Native.None
                 else
                   (match args with
                    | ({
                         FStar_Syntax_Syntax.n =
                           FStar_Syntax_Syntax.Tm_constant
                           (FStar_Const.Const_int (s, uu____5240));
                         FStar_Syntax_Syntax.pos = uu____5241;
                         FStar_Syntax_Syntax.vars = uu____5242;_},
                       uu____5243)::[] ->
                        let uu____5280 =
                          let uu____5283 = FStar_Util.int_of_string s in
                          FStar_Pervasives_Native.Some uu____5283 in
                        FStar_Pervasives_Native.Some uu____5280
                    | uu____5286 ->
                        FStar_Pervasives_Native.Some
                          FStar_Pervasives_Native.None)) in
      let uu____5299 =
        let uu____5300 = FStar_Options.codegen () in
        uu____5300 <> (FStar_Pervasives_Native.Some FStar_Options.Plugin) in
      if uu____5299
      then []
      else
        (let uu____5308 = plugin_with_arity se.FStar_Syntax_Syntax.sigattrs in
         match uu____5308 with
         | FStar_Pervasives_Native.None -> []
         | FStar_Pervasives_Native.Some arity_opt ->
             (match se.FStar_Syntax_Syntax.sigel with
              | FStar_Syntax_Syntax.Sig_let (lbs, lids) ->
                  let mk_registration lb =
                    let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                    let fv_lid =
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                    let fv_t = lb.FStar_Syntax_Syntax.lbtyp in
                    let ml_name_str =
                      let uu____5346 =
                        let uu____5347 = FStar_Ident.string_of_lid fv_lid in
                        FStar_Extraction_ML_Syntax.MLC_String uu____5347 in
                      FStar_Extraction_ML_Syntax.MLE_Const uu____5346 in
                    let uu____5348 =
                      FStar_Extraction_ML_Util.interpret_plugin_as_term_fun g
                        fv fv_t arity_opt ml_name_str in
                    match uu____5348 with
                    | FStar_Pervasives_Native.Some
                        (interp, nbe_interp, arity, plugin) ->
                        let uu____5373 =
                          if plugin
                          then
                            ((["FStar_Tactics_Native"], "register_plugin"),
                              [interp; nbe_interp])
                          else
                            ((["FStar_Tactics_Native"], "register_tactic"),
                              [interp]) in
                        (match uu____5373 with
                         | (register, args) ->
                             let h =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_Name
                                    register) in
                             let arity1 =
                               let uu____5405 =
                                 let uu____5406 =
                                   let uu____5417 =
                                     FStar_Util.string_of_int arity in
                                   (uu____5417, FStar_Pervasives_Native.None) in
                                 FStar_Extraction_ML_Syntax.MLC_Int
                                   uu____5406 in
                               FStar_Extraction_ML_Syntax.MLE_Const
                                 uu____5405 in
                             let app =
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty
                                    FStar_Extraction_ML_Syntax.MLTY_Top)
                                 (FStar_Extraction_ML_Syntax.MLE_App
                                    (h,
                                      (FStar_List.append
                                         [w ml_name_str; w arity1] args))) in
                             [FStar_Extraction_ML_Syntax.MLM_Top app])
                    | FStar_Pervasives_Native.None -> [] in
                  FStar_List.collect mk_registration
                    (FStar_Pervasives_Native.snd lbs)
              | uu____5441 -> []))
let rec (extract_sig :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t * FStar_Extraction_ML_Syntax.mlmodule1 Prims.list))
  =
  fun g ->
    fun se ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u ->
           let uu____5468 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____5468);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____5475 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____5484 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____5501 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           let uu____5517 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
           FStar_TypeChecker_Env.is_reifiable_effect uu____5517
             ed.FStar_Syntax_Syntax.mname
           ->
           let uu____5518 = extract_reifiable_effect g ed in
           (match uu____5518 with | (env, _iface, impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_splice uu____5542 ->
           failwith "impossible: trying to extract splice"
       | FStar_Syntax_Syntax.Sig_fail uu____5555 ->
           failwith "impossible: trying to extract Sig_fail"
       | FStar_Syntax_Syntax.Sig_new_effect uu____5572 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, univs, t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let uu____5578 =
             extract_type_declaration g false lid
               se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs univs t in
           (match uu____5578 with | (env, uu____5594, impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((false, lb::[]), uu____5603) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let uu____5610 =
             extract_typ_abbrev g se.FStar_Syntax_Syntax.sigquals
               se.FStar_Syntax_Syntax.sigattrs lb in
           (match uu____5610 with | (env, uu____5626, impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let ((true, lbs), uu____5635) when
           FStar_Util.for_some
             (fun lb ->
                FStar_Extraction_ML_Term.is_arity g
                  lb.FStar_Syntax_Syntax.lbtyp) lbs
           ->
           let uu____5646 = extract_let_rec_types se g lbs in
           (match uu____5646 with | (env, uu____5662, impl) -> (env, impl))
       | FStar_Syntax_Syntax.Sig_let (lbs, uu____5671) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____5682 =
             let uu____5691 =
               FStar_Syntax_Util.extract_attr'
                 FStar_Parser_Const.postprocess_extr_with attrs in
             match uu____5691 with
             | FStar_Pervasives_Native.None ->
                 (attrs, FStar_Pervasives_Native.None)
             | FStar_Pervasives_Native.Some
                 (ats, (tau, FStar_Pervasives_Native.None)::uu____5720) ->
                 (ats, (FStar_Pervasives_Native.Some tau))
             | FStar_Pervasives_Native.Some (ats, args) ->
                 (FStar_Errors.log_issue se.FStar_Syntax_Syntax.sigrng
                    (FStar_Errors.Warning_UnrecognizedAttribute,
                      "Ill-formed application of `postprocess_for_extraction_with`");
                  (attrs, FStar_Pervasives_Native.None)) in
           (match uu____5682 with
            | (attrs1, post_tau) ->
                let postprocess_lb tau lb =
                  let lbdef =
                    let uu____5804 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                    FStar_TypeChecker_Env.postprocess uu____5804 tau
                      lb.FStar_Syntax_Syntax.lbtyp
                      lb.FStar_Syntax_Syntax.lbdef in
                  let uu___967_5805 = lb in
                  {
                    FStar_Syntax_Syntax.lbname =
                      (uu___967_5805.FStar_Syntax_Syntax.lbname);
                    FStar_Syntax_Syntax.lbunivs =
                      (uu___967_5805.FStar_Syntax_Syntax.lbunivs);
                    FStar_Syntax_Syntax.lbtyp =
                      (uu___967_5805.FStar_Syntax_Syntax.lbtyp);
                    FStar_Syntax_Syntax.lbeff =
                      (uu___967_5805.FStar_Syntax_Syntax.lbeff);
                    FStar_Syntax_Syntax.lbdef = lbdef;
                    FStar_Syntax_Syntax.lbattrs =
                      (uu___967_5805.FStar_Syntax_Syntax.lbattrs);
                    FStar_Syntax_Syntax.lbpos =
                      (uu___967_5805.FStar_Syntax_Syntax.lbpos)
                  } in
                let lbs1 =
                  let uu____5813 =
                    match post_tau with
                    | FStar_Pervasives_Native.Some tau ->
                        FStar_List.map (postprocess_lb tau)
                          (FStar_Pervasives_Native.snd lbs)
                    | FStar_Pervasives_Native.None ->
                        FStar_Pervasives_Native.snd lbs in
                  ((FStar_Pervasives_Native.fst lbs), uu____5813) in
                let uu____5827 =
                  let uu____5834 =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs1, FStar_Syntax_Util.exp_false_bool))
                      se.FStar_Syntax_Syntax.sigrng in
                  FStar_Extraction_ML_Term.term_as_mlexpr g uu____5834 in
                (match uu____5827 with
                 | (ml_let, uu____5850, uu____5851) ->
                     (match ml_let.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Let
                          ((flavor, bindings), uu____5860) ->
                          let flags = FStar_List.choose flag_of_qual quals in
                          let flags' = extract_metadata attrs1 in
                          let uu____5877 =
                            FStar_List.fold_left2
                              (fun uu____5903 ->
                                 fun ml_lb ->
                                   fun uu____5905 ->
                                     match (uu____5903, uu____5905) with
                                     | ((env, ml_lbs),
                                        {
                                          FStar_Syntax_Syntax.lbname = lbname;
                                          FStar_Syntax_Syntax.lbunivs =
                                            uu____5927;
                                          FStar_Syntax_Syntax.lbtyp = t;
                                          FStar_Syntax_Syntax.lbeff =
                                            uu____5929;
                                          FStar_Syntax_Syntax.lbdef =
                                            uu____5930;
                                          FStar_Syntax_Syntax.lbattrs =
                                            uu____5931;
                                          FStar_Syntax_Syntax.lbpos =
                                            uu____5932;_})
                                         ->
                                         let uu____5957 =
                                           FStar_All.pipe_right
                                             ml_lb.FStar_Extraction_ML_Syntax.mllb_meta
                                             (FStar_List.contains
                                                FStar_Extraction_ML_Syntax.Erased) in
                                         if uu____5957
                                         then (env, ml_lbs)
                                         else
                                           (let lb_lid =
                                              let uu____5970 =
                                                let uu____5973 =
                                                  FStar_Util.right lbname in
                                                uu____5973.FStar_Syntax_Syntax.fv_name in
                                              uu____5970.FStar_Syntax_Syntax.v in
                                            let flags'' =
                                              let uu____5977 =
                                                let uu____5978 =
                                                  FStar_Syntax_Subst.compress
                                                    t in
                                                uu____5978.FStar_Syntax_Syntax.n in
                                              match uu____5977 with
                                              | FStar_Syntax_Syntax.Tm_arrow
                                                  (uu____5983,
                                                   {
                                                     FStar_Syntax_Syntax.n =
                                                       FStar_Syntax_Syntax.Comp
                                                       {
                                                         FStar_Syntax_Syntax.comp_univs
                                                           = uu____5984;
                                                         FStar_Syntax_Syntax.effect_name
                                                           = e;
                                                         FStar_Syntax_Syntax.result_typ
                                                           = uu____5986;
                                                         FStar_Syntax_Syntax.effect_args
                                                           = uu____5987;
                                                         FStar_Syntax_Syntax.flags
                                                           = uu____5988;_};
                                                     FStar_Syntax_Syntax.pos
                                                       = uu____5989;
                                                     FStar_Syntax_Syntax.vars
                                                       = uu____5990;_})
                                                  when
                                                  let uu____6025 =
                                                    FStar_Ident.string_of_lid
                                                      e in
                                                  uu____6025 =
                                                    "FStar.HyperStack.ST.StackInline"
                                                  ->
                                                  [FStar_Extraction_ML_Syntax.StackInline]
                                              | uu____6026 -> [] in
                                            let meta =
                                              FStar_List.append flags
                                                (FStar_List.append flags'
                                                   flags'') in
                                            let ml_lb1 =
                                              let uu___1015_6031 = ml_lb in
                                              {
                                                FStar_Extraction_ML_Syntax.mllb_name
                                                  =
                                                  (uu___1015_6031.FStar_Extraction_ML_Syntax.mllb_name);
                                                FStar_Extraction_ML_Syntax.mllb_tysc
                                                  =
                                                  (uu___1015_6031.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                FStar_Extraction_ML_Syntax.mllb_add_unit
                                                  =
                                                  (uu___1015_6031.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                FStar_Extraction_ML_Syntax.mllb_def
                                                  =
                                                  (uu___1015_6031.FStar_Extraction_ML_Syntax.mllb_def);
                                                FStar_Extraction_ML_Syntax.mllb_meta
                                                  = meta;
                                                FStar_Extraction_ML_Syntax.print_typ
                                                  =
                                                  (uu___1015_6031.FStar_Extraction_ML_Syntax.print_typ)
                                              } in
                                            let uu____6032 =
                                              let uu____6037 =
                                                FStar_All.pipe_right quals
                                                  (FStar_Util.for_some
                                                     (fun uu___9_6042 ->
                                                        match uu___9_6042
                                                        with
                                                        | FStar_Syntax_Syntax.Projector
                                                            uu____6043 ->
                                                            true
                                                        | uu____6048 -> false)) in
                                              if uu____6037
                                              then
                                                let uu____6053 =
                                                  let uu____6060 =
                                                    FStar_Util.right lbname in
                                                  let uu____6061 =
                                                    FStar_Util.must
                                                      ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                                  FStar_Extraction_ML_UEnv.extend_fv
                                                    env uu____6060 uu____6061
                                                    ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit in
                                                match uu____6053 with
                                                | (env1, mls, uu____6068) ->
                                                    (env1,
                                                      (let uu___1027_6070 =
                                                         ml_lb1 in
                                                       {
                                                         FStar_Extraction_ML_Syntax.mllb_name
                                                           = mls;
                                                         FStar_Extraction_ML_Syntax.mllb_tysc
                                                           =
                                                           (uu___1027_6070.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                         FStar_Extraction_ML_Syntax.mllb_add_unit
                                                           =
                                                           (uu___1027_6070.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                         FStar_Extraction_ML_Syntax.mllb_def
                                                           =
                                                           (uu___1027_6070.FStar_Extraction_ML_Syntax.mllb_def);
                                                         FStar_Extraction_ML_Syntax.mllb_meta
                                                           =
                                                           (uu___1027_6070.FStar_Extraction_ML_Syntax.mllb_meta);
                                                         FStar_Extraction_ML_Syntax.print_typ
                                                           =
                                                           (uu___1027_6070.FStar_Extraction_ML_Syntax.print_typ)
                                                       }))
                                              else
                                                (let uu____6072 =
                                                   let uu____6079 =
                                                     FStar_Util.must
                                                       ml_lb1.FStar_Extraction_ML_Syntax.mllb_tysc in
                                                   FStar_Extraction_ML_UEnv.extend_lb
                                                     env lbname t uu____6079
                                                     ml_lb1.FStar_Extraction_ML_Syntax.mllb_add_unit in
                                                 match uu____6072 with
                                                 | (env1, uu____6085,
                                                    uu____6086) ->
                                                     (env1, ml_lb1)) in
                                            match uu____6032 with
                                            | (g1, ml_lb2) ->
                                                (g1, (ml_lb2 :: ml_lbs))))
                              (g, []) bindings
                              (FStar_Pervasives_Native.snd lbs1) in
                          (match uu____5877 with
                           | (g1, ml_lbs') ->
                               let uu____6113 =
                                 let uu____6116 =
                                   let uu____6119 =
                                     let uu____6120 =
                                       FStar_Extraction_ML_Util.mlloc_of_range
                                         se.FStar_Syntax_Syntax.sigrng in
                                     FStar_Extraction_ML_Syntax.MLM_Loc
                                       uu____6120 in
                                   [uu____6119;
                                   FStar_Extraction_ML_Syntax.MLM_Let
                                     (flavor, (FStar_List.rev ml_lbs'))] in
                                 let uu____6123 = maybe_register_plugin g1 se in
                                 FStar_List.append uu____6116 uu____6123 in
                               (g1, uu____6113))
                      | uu____6128 ->
                          let uu____6129 =
                            let uu____6130 =
                              let uu____6131 =
                                FStar_Extraction_ML_UEnv.current_module_of_uenv
                                  g in
                              FStar_Extraction_ML_Code.string_of_mlexpr
                                uu____6131 ml_let in
                            FStar_Util.format1
                              "Impossible: Translated a let to a non-let: %s"
                              uu____6130 in
                          failwith uu____6129)))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid, uu____6139, t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____6144 =
             (FStar_All.pipe_right quals
                (FStar_List.contains FStar_Syntax_Syntax.Assumption))
               &&
               (let uu____6148 =
                  let uu____6149 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g in
                  FStar_TypeChecker_Util.must_erase_for_extraction uu____6149
                    t in
                Prims.op_Negation uu____6148) in
           if uu____6144
           then
             let always_fail1 =
               let uu___1047_6157 = se in
               let uu____6158 =
                 let uu____6159 =
                   let uu____6166 =
                     let uu____6167 =
                       let uu____6170 = always_fail lid t in [uu____6170] in
                     (false, uu____6167) in
                   (uu____6166, []) in
                 FStar_Syntax_Syntax.Sig_let uu____6159 in
               {
                 FStar_Syntax_Syntax.sigel = uu____6158;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___1047_6157.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___1047_6157.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___1047_6157.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___1047_6157.FStar_Syntax_Syntax.sigattrs);
                 FStar_Syntax_Syntax.sigopts =
                   (uu___1047_6157.FStar_Syntax_Syntax.sigopts)
               } in
             let uu____6175 = extract_sig g always_fail1 in
             (match uu____6175 with
              | (g1, mlm) ->
                  let uu____6194 =
                    FStar_Util.find_map quals
                      (fun uu___10_6199 ->
                         match uu___10_6199 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____6203 -> FStar_Pervasives_Native.None) in
                  (match uu____6194 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____6211 =
                         let uu____6214 =
                           let uu____6215 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____6215 in
                         let uu____6216 =
                           let uu____6219 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____6219] in
                         uu____6214 :: uu____6216 in
                       (g1, uu____6211)
                   | uu____6222 ->
                       let uu____6225 =
                         FStar_Util.find_map quals
                           (fun uu___11_6231 ->
                              match uu___11_6231 with
                              | FStar_Syntax_Syntax.Projector (l, uu____6235)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____6236 -> FStar_Pervasives_Native.None) in
                       (match uu____6225 with
                        | FStar_Pervasives_Native.Some uu____6243 -> (g1, [])
                        | uu____6246 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_assume uu____6254 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____6263 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____6266 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_bind uu____6281 -> (g, [])
       | FStar_Syntax_Syntax.Sig_polymonadic_subcomp uu____6294 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (FStar_Syntax_Util.process_pragma p se.FStar_Syntax_Syntax.sigrng;
            (g, [])))
let (extract' :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      let uu____6331 = FStar_Options.restore_cmd_line_options true in
      let uu____6332 =
        FStar_Extraction_ML_UEnv.extend_with_module_name g
          m.FStar_Syntax_Syntax.name in
      match uu____6332 with
      | (name, g1) ->
          let g2 =
            let uu____6346 =
              let uu____6347 = FStar_Extraction_ML_UEnv.tcenv_of_uenv g1 in
              FStar_TypeChecker_Env.set_current_module uu____6347
                m.FStar_Syntax_Syntax.name in
            FStar_Extraction_ML_UEnv.set_tcenv g1 uu____6346 in
          let g3 = FStar_Extraction_ML_UEnv.set_current_module g2 name in
          let uu____6349 =
            FStar_Util.fold_map
              (fun g4 ->
                 fun se ->
                   let uu____6368 =
                     let uu____6369 =
                       FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                     FStar_Options.debug_module uu____6369 in
                   if uu____6368
                   then
                     let nm =
                       let uu____6377 =
                         FStar_All.pipe_right
                           (FStar_Syntax_Util.lids_of_sigelt se)
                           (FStar_List.map FStar_Ident.string_of_lid) in
                       FStar_All.pipe_right uu____6377
                         (FStar_String.concat ", ") in
                     (FStar_Util.print1 "+++About to extract {%s}\n" nm;
                      (let uu____6387 =
                         FStar_Util.format1 "---Extracted {%s}" nm in
                       FStar_Util.measure_execution_time uu____6387
                         (fun uu____6395 -> extract_sig g4 se)))
                   else extract_sig g4 se) g3
              m.FStar_Syntax_Syntax.declarations in
          (match uu____6349 with
           | (g4, sigs) ->
               let mlm = FStar_List.flatten sigs in
               let is_kremlin =
                 let uu____6415 = FStar_Options.codegen () in
                 uu____6415 =
                   (FStar_Pervasives_Native.Some FStar_Options.Kremlin) in
               let uu____6420 =
                 (let uu____6423 =
                    FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                  uu____6423 <> "Prims") &&
                   (is_kremlin ||
                      (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)) in
               if uu____6420
               then
                 ((let uu____6431 =
                     let uu____6432 = FStar_Options.silent () in
                     Prims.op_Negation uu____6432 in
                   if uu____6431
                   then
                     let uu____6433 =
                       FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
                     FStar_Util.print1 "Extracted module %s\n" uu____6433
                   else ());
                  (g4,
                    (FStar_Pervasives_Native.Some
                       (FStar_Extraction_ML_Syntax.MLLib
                          [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                             (FStar_Extraction_ML_Syntax.MLLib []))]))))
               else (g4, FStar_Pervasives_Native.None))
let (extract :
  FStar_Extraction_ML_UEnv.uenv ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.uenv * FStar_Extraction_ML_Syntax.mllib
        FStar_Pervasives_Native.option))
  =
  fun g ->
    fun m ->
      (let uu____6503 = FStar_Options.restore_cmd_line_options true in
       FStar_All.pipe_left (fun uu____6504 -> ()) uu____6503);
      (let uu____6506 =
         let uu____6507 =
           let uu____6508 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Options.should_extract uu____6508 in
         Prims.op_Negation uu____6507 in
       if uu____6506
       then
         let uu____6509 =
           let uu____6510 =
             FStar_Ident.string_of_lid m.FStar_Syntax_Syntax.name in
           FStar_Util.format1
             "Extract called on a module %s that should not be extracted"
             uu____6510 in
         failwith uu____6509
       else ());
      (let uu____6512 = FStar_Options.interactive () in
       if uu____6512
       then (g, FStar_Pervasives_Native.None)
       else
         (let uu____6522 =
            FStar_Syntax_Unionfind.with_uf_enabled
              (fun uu____6538 ->
                 let uu____6539 = FStar_Options.debug_any () in
                 if uu____6539
                 then
                   let msg =
                     let uu____6547 =
                       FStar_Syntax_Print.lid_to_string
                         m.FStar_Syntax_Syntax.name in
                     FStar_Util.format1 "Extracting module %s" uu____6547 in
                   FStar_Util.measure_execution_time msg
                     (fun uu____6555 -> extract' g m)
                 else extract' g m) in
          match uu____6522 with
          | (g1, mllib) ->
              let uu____6569 =
                match mllib with
                | FStar_Pervasives_Native.None -> (g1, mllib)
                | FStar_Pervasives_Native.Some mllib1 ->
                    let uu____6585 =
                      FStar_Extraction_ML_UEnv.with_typars_env g1
                        (fun e ->
                           FStar_Extraction_ML_RemoveUnusedParameters.elim_mllib
                             e mllib1) in
                    (match uu____6585 with
                     | (g2, mllib2) ->
                         (g2, (FStar_Pervasives_Native.Some mllib2))) in
              (match uu____6569 with
               | (g2, mllib1) ->
                   ((let uu____6615 =
                       FStar_Options.restore_cmd_line_options true in
                     FStar_All.pipe_left (fun uu____6616 -> ()) uu____6615);
                    (let uu____6617 = FStar_Extraction_ML_UEnv.exit_module g2 in
                     (uu____6617, mllib1))))))