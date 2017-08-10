open Prims
let fail_exp:
  FStar_Ident.lident ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax
  =
  fun lid  ->
    fun t  ->
      let uu____11 =
        let uu____14 =
          let uu____15 =
            let uu____30 =
              FStar_Syntax_Syntax.fvar FStar_Parser_Const.failwith_lid
                FStar_Syntax_Syntax.Delta_constant
                FStar_Pervasives_Native.None in
            let uu____31 =
              let uu____34 = FStar_Syntax_Syntax.iarg t in
              let uu____35 =
                let uu____38 =
                  let uu____39 =
                    let uu____40 =
                      let uu____43 =
                        let uu____44 =
                          let uu____45 =
                            let uu____52 =
                              let uu____53 =
                                let uu____54 =
                                  FStar_Syntax_Print.lid_to_string lid in
                                Prims.strcat "Not yet implemented:" uu____54 in
                              FStar_Bytes.string_as_unicode_bytes uu____53 in
                            (uu____52, FStar_Range.dummyRange) in
                          FStar_Const.Const_string uu____45 in
                        FStar_Syntax_Syntax.Tm_constant uu____44 in
                      FStar_Syntax_Syntax.mk uu____43 in
                    uu____40 FStar_Pervasives_Native.None
                      FStar_Range.dummyRange in
                  FStar_All.pipe_left FStar_Syntax_Syntax.as_arg uu____39 in
                [uu____38] in
              uu____34 :: uu____35 in
            (uu____30, uu____31) in
          FStar_Syntax_Syntax.Tm_app uu____15 in
        FStar_Syntax_Syntax.mk uu____14 in
      uu____11 FStar_Pervasives_Native.None FStar_Range.dummyRange
let mangle_projector_lid: FStar_Ident.lident -> FStar_Ident.lident =
  fun x  -> x
let lident_as_mlsymbol:
  FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlsymbol =
  fun id  -> (id.FStar_Ident.ident).FStar_Ident.idText
let as_pair:
  'Auu____75 .
    'Auu____75 Prims.list ->
      ('Auu____75,'Auu____75) FStar_Pervasives_Native.tuple2
  =
  fun uu___151_85  ->
    match uu___151_85 with
    | a::b::[] -> (a, b)
    | uu____90 -> failwith "Expected a list with 2 elements"
let rec extract_attr:
  FStar_Syntax_Syntax.term ->
    FStar_Extraction_ML_Syntax.attr FStar_Pervasives_Native.option
  =
  fun x  ->
    let uu____103 = FStar_Syntax_Subst.compress x in
    match uu____103 with
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____107;
        FStar_Syntax_Syntax.vars = uu____108;_} when
        let uu____111 =
          let uu____112 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____112 in
        uu____111 = "FStar.Pervasives.PpxDerivingShow" ->
        FStar_Pervasives_Native.Some
          FStar_Extraction_ML_Syntax.PpxDerivingShow
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____114;
        FStar_Syntax_Syntax.vars = uu____115;_} when
        let uu____118 =
          let uu____119 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____119 in
        uu____118 = "FStar.Pervasives.CInline" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.CInline
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____121;
        FStar_Syntax_Syntax.vars = uu____122;_} when
        let uu____125 =
          let uu____126 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____126 in
        uu____125 = "FStar.Pervasives.Substitute" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.Substitute
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
        FStar_Syntax_Syntax.pos = uu____128;
        FStar_Syntax_Syntax.vars = uu____129;_} when
        let uu____132 =
          let uu____133 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____133 in
        uu____132 = "FStar.Pervasives.Gc" ->
        FStar_Pervasives_Native.Some FStar_Extraction_ML_Syntax.GCType
    | {
        FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____135;
             FStar_Syntax_Syntax.vars = uu____136;_},({
                                                        FStar_Syntax_Syntax.n
                                                          =
                                                          FStar_Syntax_Syntax.Tm_constant
                                                          (FStar_Const.Const_string
                                                          (data,uu____138));
                                                        FStar_Syntax_Syntax.pos
                                                          = uu____139;
                                                        FStar_Syntax_Syntax.vars
                                                          = uu____140;_},uu____141)::[]);
        FStar_Syntax_Syntax.pos = uu____142;
        FStar_Syntax_Syntax.vars = uu____143;_} when
        let uu____178 =
          let uu____179 = FStar_Syntax_Syntax.lid_of_fv fv in
          FStar_Ident.string_of_lid uu____179 in
        uu____178 = "FStar.Pervasives.PpxDerivingShowConstant" ->
        FStar_Pervasives_Native.Some
          (FStar_Extraction_ML_Syntax.PpxDerivingShowConstant
             (FStar_Util.string_of_unicode data))
    | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_meta (x1,uu____181);
        FStar_Syntax_Syntax.pos = uu____182;
        FStar_Syntax_Syntax.vars = uu____183;_} -> extract_attr x1
    | a ->
        ((let uu____192 = FStar_Syntax_Print.term_to_string a in
          FStar_Util.print1_warning
            "Warning: unrecognized attribute (%s), valid attributes are `c_inline`, `substitute`, and `gc`."
            uu____192);
         FStar_Pervasives_Native.None)
let extract_attrs:
  FStar_Syntax_Syntax.term Prims.list ->
    FStar_Extraction_ML_Syntax.attr Prims.list
  = fun attrs  -> FStar_List.choose extract_attr attrs
let binders_as_mlty_binders:
  'Auu____209 .
    FStar_Extraction_ML_UEnv.env ->
      (FStar_Syntax_Syntax.bv,'Auu____209) FStar_Pervasives_Native.tuple2
        Prims.list ->
        (FStar_Extraction_ML_UEnv.env,(Prims.string,Prims.int)
                                        FStar_Pervasives_Native.tuple2
                                        Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bs  ->
      FStar_Util.fold_map
        (fun env1  ->
           fun uu____255  ->
             match uu____255 with
             | (bv,uu____269) ->
                 let uu____270 =
                   let uu____271 =
                     let uu____274 =
                       let uu____275 =
                         FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                       FStar_Extraction_ML_Syntax.MLTY_Var uu____275 in
                     FStar_Pervasives_Native.Some uu____274 in
                   FStar_Extraction_ML_UEnv.extend_ty env1 bv uu____271 in
                 let uu____276 = FStar_Extraction_ML_UEnv.bv_as_ml_tyvar bv in
                 (uu____270, uu____276)) env bs
let extract_typ_abbrev:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        FStar_Syntax_Syntax.term Prims.list ->
          FStar_Syntax_Syntax.term ->
            (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mlmodule1
                                            Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun fv  ->
      fun quals  ->
        fun attrs  ->
          fun def  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let def1 =
              let uu____321 =
                let uu____322 = FStar_Syntax_Subst.compress def in
                FStar_All.pipe_right uu____322 FStar_Syntax_Util.unmeta in
              FStar_All.pipe_right uu____321 FStar_Syntax_Util.un_uinst in
            let def2 =
              match def1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs uu____324 ->
                  FStar_Extraction_ML_Term.normalize_abs def1
              | uu____341 -> def1 in
            let uu____342 =
              match def2.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_abs (bs,body,uu____353) ->
                  FStar_Syntax_Subst.open_term bs body
              | uu____374 -> ([], def2) in
            match uu____342 with
            | (bs,body) ->
                let assumed =
                  FStar_Util.for_some
                    (fun uu___152_395  ->
                       match uu___152_395 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____396 -> false) quals in
                let uu____397 = binders_as_mlty_binders env bs in
                (match uu____397 with
                 | (env1,ml_bs) ->
                     let body1 =
                       let uu____429 =
                         FStar_Extraction_ML_Term.term_as_mlty env1 body in
                       FStar_All.pipe_right uu____429
                         (FStar_Extraction_ML_Util.eraseTypeDeep
                            (FStar_Extraction_ML_Util.udelta_unfold env1)) in
                     let mangled_projector =
                       let uu____433 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___153_438  ->
                                 match uu___153_438 with
                                 | FStar_Syntax_Syntax.Projector uu____439 ->
                                     true
                                 | uu____444 -> false)) in
                       if uu____433
                       then
                         let mname = mangle_projector_lid lid in
                         FStar_Pervasives_Native.Some
                           ((mname.FStar_Ident.ident).FStar_Ident.idText)
                       else FStar_Pervasives_Native.None in
                     let attrs1 = extract_attrs attrs in
                     let td =
                       let uu____479 =
                         let uu____504 = lident_as_mlsymbol lid in
                         (assumed, uu____504, mangled_projector, ml_bs,
                           attrs1,
                           (FStar_Pervasives_Native.Some
                              (FStar_Extraction_ML_Syntax.MLTD_Abbrev body1))) in
                       [uu____479] in
                     let def3 =
                       let uu____568 =
                         let uu____569 =
                           FStar_Extraction_ML_Util.mlloc_of_range
                             (FStar_Ident.range_of_lid lid) in
                         FStar_Extraction_ML_Syntax.MLM_Loc uu____569 in
                       [uu____568; FStar_Extraction_ML_Syntax.MLM_Ty td] in
                     let env2 =
                       let uu____571 =
                         FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___154_575  ->
                                 match uu___154_575 with
                                 | FStar_Syntax_Syntax.Assumption  -> true
                                 | FStar_Syntax_Syntax.New  -> true
                                 | uu____576 -> false)) in
                       if uu____571
                       then FStar_Extraction_ML_UEnv.extend_type_name env1 fv
                       else FStar_Extraction_ML_UEnv.extend_tydef env1 fv td in
                     (env2, def3))
type data_constructor =
  {
  dname: FStar_Ident.lident;
  dtyp: FStar_Syntax_Syntax.typ;}
let __proj__Mkdata_constructor__item__dname:
  data_constructor -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dname
let __proj__Mkdata_constructor__item__dtyp:
  data_constructor -> FStar_Syntax_Syntax.typ =
  fun projectee  ->
    match projectee with
    | { dname = __fname__dname; dtyp = __fname__dtyp;_} -> __fname__dtyp
type inductive_family =
  {
  iname: FStar_Ident.lident;
  iparams: FStar_Syntax_Syntax.binders;
  ityp: FStar_Syntax_Syntax.term;
  idatas: data_constructor Prims.list;
  iquals: FStar_Syntax_Syntax.qualifier Prims.list;
  iattrs: FStar_Extraction_ML_Syntax.attrs;}
let __proj__Mkinductive_family__item__iname:
  inductive_family -> FStar_Ident.lident =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iname
let __proj__Mkinductive_family__item__iparams:
  inductive_family -> FStar_Syntax_Syntax.binders =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iparams
let __proj__Mkinductive_family__item__ityp:
  inductive_family -> FStar_Syntax_Syntax.term =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__ityp
let __proj__Mkinductive_family__item__idatas:
  inductive_family -> data_constructor Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__idatas
let __proj__Mkinductive_family__item__iquals:
  inductive_family -> FStar_Syntax_Syntax.qualifier Prims.list =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iquals
let __proj__Mkinductive_family__item__iattrs:
  inductive_family -> FStar_Extraction_ML_Syntax.attrs =
  fun projectee  ->
    match projectee with
    | { iname = __fname__iname; iparams = __fname__iparams;
        ityp = __fname__ityp; idatas = __fname__idatas;
        iquals = __fname__iquals; iattrs = __fname__iattrs;_} ->
        __fname__iattrs
let print_ifamily: inductive_family -> Prims.unit =
  fun i  ->
    let uu____724 = FStar_Syntax_Print.lid_to_string i.iname in
    let uu____725 = FStar_Syntax_Print.binders_to_string " " i.iparams in
    let uu____726 = FStar_Syntax_Print.term_to_string i.ityp in
    let uu____727 =
      let uu____728 =
        FStar_All.pipe_right i.idatas
          (FStar_List.map
             (fun d  ->
                let uu____739 = FStar_Syntax_Print.lid_to_string d.dname in
                let uu____740 =
                  let uu____741 = FStar_Syntax_Print.term_to_string d.dtyp in
                  Prims.strcat " : " uu____741 in
                Prims.strcat uu____739 uu____740)) in
      FStar_All.pipe_right uu____728 (FStar_String.concat "\n\t\t") in
    FStar_Util.print4 "\n\t%s %s : %s { %s }\n" uu____724 uu____725 uu____726
      uu____727
let bundle_as_inductive_families:
  'Auu____754 .
    FStar_Extraction_ML_UEnv.env ->
      FStar_Syntax_Syntax.sigelt Prims.list ->
        'Auu____754 ->
          FStar_Syntax_Syntax.attribute Prims.list ->
            (FStar_Extraction_ML_UEnv.env,inductive_family Prims.list)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      fun quals  ->
        fun attrs  ->
          let uu____785 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun se  ->
                   match se.FStar_Syntax_Syntax.sigel with
                   | FStar_Syntax_Syntax.Sig_inductive_typ
                       (l,_us,bs,t,_mut_i,datas) ->
                       let uu____832 = FStar_Syntax_Subst.open_term bs t in
                       (match uu____832 with
                        | (bs1,t1) ->
                            let datas1 =
                              FStar_All.pipe_right ses
                                (FStar_List.collect
                                   (fun se1  ->
                                      match se1.FStar_Syntax_Syntax.sigel
                                      with
                                      | FStar_Syntax_Syntax.Sig_datacon
                                          (d,uu____871,t2,l',nparams,uu____875)
                                          when FStar_Ident.lid_equals l l' ->
                                          let uu____880 =
                                            FStar_Syntax_Util.arrow_formals
                                              t2 in
                                          (match uu____880 with
                                           | (bs',body) ->
                                               let uu____913 =
                                                 FStar_Util.first_N
                                                   (FStar_List.length bs1)
                                                   bs' in
                                               (match uu____913 with
                                                | (bs_params,rest) ->
                                                    let subst1 =
                                                      FStar_List.map2
                                                        (fun uu____984  ->
                                                           fun uu____985  ->
                                                             match (uu____984,
                                                                    uu____985)
                                                             with
                                                             | ((b',uu____1003),
                                                                (b,uu____1005))
                                                                 ->
                                                                 let uu____1014
                                                                   =
                                                                   let uu____1021
                                                                    =
                                                                    FStar_Syntax_Syntax.bv_to_name
                                                                    b in
                                                                   (b',
                                                                    uu____1021) in
                                                                 FStar_Syntax_Syntax.NT
                                                                   uu____1014)
                                                        bs_params bs1 in
                                                    let t3 =
                                                      let uu____1023 =
                                                        let uu____1026 =
                                                          FStar_Syntax_Syntax.mk_Total
                                                            body in
                                                        FStar_Syntax_Util.arrow
                                                          rest uu____1026 in
                                                      FStar_All.pipe_right
                                                        uu____1023
                                                        (FStar_Syntax_Subst.subst
                                                           subst1) in
                                                    [{ dname = d; dtyp = t3 }]))
                                      | uu____1031 -> [])) in
                            let attrs1 =
                              extract_attrs
                                (FStar_List.append
                                   se.FStar_Syntax_Syntax.sigattrs attrs) in
                            let env2 =
                              let uu____1036 =
                                FStar_Syntax_Syntax.lid_as_fv l
                                  FStar_Syntax_Syntax.Delta_constant
                                  FStar_Pervasives_Native.None in
                              FStar_Extraction_ML_UEnv.extend_type_name env1
                                uu____1036 in
                            (env2,
                              [{
                                 iname = l;
                                 iparams = bs1;
                                 ityp = t1;
                                 idatas = datas1;
                                 iquals = (se.FStar_Syntax_Syntax.sigquals);
                                 iattrs = attrs1
                               }]))
                   | uu____1039 -> (env1, [])) env ses in
          match uu____785 with
          | (env1,ifams) -> (env1, (FStar_List.flatten ifams))
type env_t = FStar_Extraction_ML_UEnv.env
let extract_bundle:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let extract_ctor ml_tyvars env1 ctor =
        let mlt =
          let uu____1125 =
            FStar_Extraction_ML_Term.term_as_mlty env1 ctor.dtyp in
          FStar_Extraction_ML_Util.eraseTypeDeep
            (FStar_Extraction_ML_Util.udelta_unfold env1) uu____1125 in
        let steps =
          [FStar_TypeChecker_Normalize.Inlining;
          FStar_TypeChecker_Normalize.UnfoldUntil
            FStar_Syntax_Syntax.Delta_constant;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] in
        let names1 =
          let uu____1132 =
            let uu____1133 =
              let uu____1136 =
                FStar_TypeChecker_Normalize.normalize steps
                  env1.FStar_Extraction_ML_UEnv.tcenv ctor.dtyp in
              FStar_Syntax_Subst.compress uu____1136 in
            uu____1133.FStar_Syntax_Syntax.n in
          match uu____1132 with
          | FStar_Syntax_Syntax.Tm_arrow (bs,uu____1140) ->
              FStar_List.map
                (fun uu____1166  ->
                   match uu____1166 with
                   | ({ FStar_Syntax_Syntax.ppname = ppname;
                        FStar_Syntax_Syntax.index = uu____1172;
                        FStar_Syntax_Syntax.sort = uu____1173;_},uu____1174)
                       -> ppname.FStar_Ident.idText) bs
          | uu____1177 -> [] in
        let tys = (ml_tyvars, mlt) in
        let fvv = FStar_Extraction_ML_UEnv.mkFvvar ctor.dname ctor.dtyp in
        let uu____1196 =
          let uu____1197 =
            FStar_Extraction_ML_UEnv.extend_fv env1 fvv tys false false in
          FStar_Pervasives_Native.fst uu____1197 in
        let uu____1202 =
          let uu____1213 = lident_as_mlsymbol ctor.dname in
          let uu____1214 =
            let uu____1221 = FStar_Extraction_ML_Util.argTypes mlt in
            FStar_List.zip names1 uu____1221 in
          (uu____1213, uu____1214) in
        (uu____1196, uu____1202) in
      let extract_one_family env1 ind =
        let uu____1273 = binders_as_mlty_binders env1 ind.iparams in
        match uu____1273 with
        | (env2,vars) ->
            let uu____1324 =
              FStar_All.pipe_right ind.idatas
                (FStar_Util.fold_map (extract_ctor vars) env2) in
            (match uu____1324 with
             | (env3,ctors) ->
                 let uu____1421 = FStar_Syntax_Util.arrow_formals ind.ityp in
                 (match uu____1421 with
                  | (indices,uu____1461) ->
                      let ml_params =
                        let uu____1485 =
                          FStar_All.pipe_right indices
                            (FStar_List.mapi
                               (fun i  ->
                                  fun uu____1516  ->
                                    let uu____1521 =
                                      let uu____1522 =
                                        FStar_Util.string_of_int i in
                                      Prims.strcat "'dummyV" uu____1522 in
                                    (uu____1521, (Prims.parse_int "0")))) in
                        FStar_List.append vars uu____1485 in
                      let tbody =
                        let uu____1528 =
                          FStar_Util.find_opt
                            (fun uu___155_1533  ->
                               match uu___155_1533 with
                               | FStar_Syntax_Syntax.RecordType uu____1534 ->
                                   true
                               | uu____1543 -> false) ind.iquals in
                        match uu____1528 with
                        | FStar_Pervasives_Native.Some
                            (FStar_Syntax_Syntax.RecordType (ns,ids)) ->
                            let uu____1554 = FStar_List.hd ctors in
                            (match uu____1554 with
                             | (uu____1575,c_ty) ->
                                 let fields =
                                   FStar_List.map2
                                     (fun id  ->
                                        fun uu____1614  ->
                                          match uu____1614 with
                                          | (uu____1623,ty) ->
                                              let lid =
                                                FStar_Ident.lid_of_ids
                                                  (FStar_List.append ns [id]) in
                                              let uu____1626 =
                                                lident_as_mlsymbol lid in
                                              (uu____1626, ty)) ids c_ty in
                                 FStar_Extraction_ML_Syntax.MLTD_Record
                                   fields)
                        | uu____1627 ->
                            FStar_Extraction_ML_Syntax.MLTD_DType ctors in
                      let uu____1630 =
                        let uu____1653 = lident_as_mlsymbol ind.iname in
                        (false, uu____1653, FStar_Pervasives_Native.None,
                          ml_params, (ind.iattrs),
                          (FStar_Pervasives_Native.Some tbody)) in
                      (env3, uu____1630))) in
      match ((se.FStar_Syntax_Syntax.sigel),
              (se.FStar_Syntax_Syntax.sigquals))
      with
      | (FStar_Syntax_Syntax.Sig_bundle
         ({
            FStar_Syntax_Syntax.sigel = FStar_Syntax_Syntax.Sig_datacon
              (l,uu____1695,t,uu____1697,uu____1698,uu____1699);
            FStar_Syntax_Syntax.sigrng = uu____1700;
            FStar_Syntax_Syntax.sigquals = uu____1701;
            FStar_Syntax_Syntax.sigmeta = uu____1702;
            FStar_Syntax_Syntax.sigattrs = uu____1703;_}::[],uu____1704),(FStar_Syntax_Syntax.ExceptionConstructor
         )::[]) ->
          let uu____1721 = extract_ctor [] env { dname = l; dtyp = t } in
          (match uu____1721 with
           | (env1,ctor) -> (env1, [FStar_Extraction_ML_Syntax.MLM_Exn ctor]))
      | (FStar_Syntax_Syntax.Sig_bundle (ses,uu____1771),quals) ->
          let uu____1785 =
            bundle_as_inductive_families env ses quals
              se.FStar_Syntax_Syntax.sigattrs in
          (match uu____1785 with
           | (env1,ifams) ->
               let uu____1806 =
                 FStar_Util.fold_map extract_one_family env1 ifams in
               (match uu____1806 with
                | (env2,td) -> (env2, [FStar_Extraction_ML_Syntax.MLM_Ty td])))
      | uu____1915 -> failwith "Unexpected signature element"
let rec extract_sig:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (env_t,FStar_Extraction_ML_Syntax.mlmodule1 Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun se  ->
      FStar_Extraction_ML_UEnv.debug g
        (fun u  ->
           let uu____1952 = FStar_Syntax_Print.sigelt_to_string se in
           FStar_Util.print1 ">>>> extract_sig %s \n" uu____1952);
      (match se.FStar_Syntax_Syntax.sigel with
       | FStar_Syntax_Syntax.Sig_bundle uu____1959 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_inductive_typ uu____1968 ->
           extract_bundle g se
       | FStar_Syntax_Syntax.Sig_datacon uu____1985 -> extract_bundle g se
       | FStar_Syntax_Syntax.Sig_new_effect ed when
           FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
           ->
           let extend_env g1 lid ml_name tm tysc =
             let uu____2023 =
               let uu____2028 =
                 FStar_Syntax_Syntax.lid_as_fv lid
                   FStar_Syntax_Syntax.Delta_equational
                   FStar_Pervasives_Native.None in
               FStar_Extraction_ML_UEnv.extend_fv' g1 uu____2028 ml_name tysc
                 false false in
             match uu____2023 with
             | (g2,mangled_name) ->
                 ((let uu____2036 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug
                          g2.FStar_Extraction_ML_UEnv.tcenv)
                       (FStar_Options.Other "ExtractionReify") in
                   if uu____2036
                   then
                     FStar_Util.print1 "Mangled name: %s\n"
                       (FStar_Pervasives_Native.fst mangled_name)
                   else ());
                  (let lb =
                     {
                       FStar_Extraction_ML_Syntax.mllb_name = mangled_name;
                       FStar_Extraction_ML_Syntax.mllb_tysc =
                         FStar_Pervasives_Native.None;
                       FStar_Extraction_ML_Syntax.mllb_add_unit = false;
                       FStar_Extraction_ML_Syntax.mllb_def = tm;
                       FStar_Extraction_ML_Syntax.print_typ = false
                     } in
                   (g2,
                     (FStar_Extraction_ML_Syntax.MLM_Let
                        (FStar_Extraction_ML_Syntax.NonRec, [], [lb]))))) in
           let rec extract_fv tm =
             (let uu____2052 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2052
              then
                let uu____2053 = FStar_Syntax_Print.term_to_string tm in
                FStar_Util.print1 "extract_fv term: %s\n" uu____2053
              else ());
             (let uu____2055 =
                let uu____2056 = FStar_Syntax_Subst.compress tm in
                uu____2056.FStar_Syntax_Syntax.n in
              match uu____2055 with
              | FStar_Syntax_Syntax.Tm_uinst (tm1,uu____2064) ->
                  extract_fv tm1
              | FStar_Syntax_Syntax.Tm_fvar fv ->
                  let mlp =
                    FStar_Extraction_ML_Syntax.mlpath_of_lident
                      (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                  let uu____2071 =
                    let uu____2080 = FStar_Extraction_ML_UEnv.lookup_fv g fv in
                    FStar_All.pipe_left FStar_Util.right uu____2080 in
                  (match uu____2071 with
                   | (uu____2137,uu____2138,tysc,uu____2140) ->
                       let uu____2141 =
                         FStar_All.pipe_left
                           (FStar_Extraction_ML_Syntax.with_ty
                              FStar_Extraction_ML_Syntax.MLTY_Top)
                           (FStar_Extraction_ML_Syntax.MLE_Name mlp) in
                       (uu____2141, tysc))
              | uu____2142 -> failwith "Not an fv") in
           let extract_action g1 a =
             (let uu____2168 =
                FStar_All.pipe_left
                  (FStar_TypeChecker_Env.debug
                     g1.FStar_Extraction_ML_UEnv.tcenv)
                  (FStar_Options.Other "ExtractionReify") in
              if uu____2168
              then
                let uu____2169 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_typ in
                let uu____2170 =
                  FStar_Syntax_Print.term_to_string
                    a.FStar_Syntax_Syntax.action_defn in
                FStar_Util.print2 "Action type %s and term %s\n" uu____2169
                  uu____2170
              else ());
             (let uu____2172 = FStar_Extraction_ML_UEnv.action_name ed a in
              match uu____2172 with
              | (a_nm,a_lid) ->
                  let lbname =
                    let uu____2188 =
                      FStar_Syntax_Syntax.new_bv
                        (FStar_Pervasives_Native.Some
                           ((a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos))
                        FStar_Syntax_Syntax.tun in
                    FStar_Util.Inl uu____2188 in
                  let lb =
                    FStar_Syntax_Syntax.mk_lb
                      (lbname, (a.FStar_Syntax_Syntax.action_univs),
                        FStar_Parser_Const.effect_Tot_lid,
                        (a.FStar_Syntax_Syntax.action_typ),
                        (a.FStar_Syntax_Syntax.action_defn)) in
                  let lbs = (false, [lb]) in
                  let action_lb =
                    FStar_Syntax_Syntax.mk
                      (FStar_Syntax_Syntax.Tm_let
                         (lbs, FStar_Syntax_Util.exp_false_bool))
                      FStar_Pervasives_Native.None
                      (a.FStar_Syntax_Syntax.action_defn).FStar_Syntax_Syntax.pos in
                  let uu____2214 =
                    FStar_Extraction_ML_Term.term_as_mlexpr g1 action_lb in
                  (match uu____2214 with
                   | (a_let,uu____2226,ty) ->
                       ((let uu____2229 =
                           FStar_All.pipe_left
                             (FStar_TypeChecker_Env.debug
                                g1.FStar_Extraction_ML_UEnv.tcenv)
                             (FStar_Options.Other "ExtractionReify") in
                         if uu____2229
                         then
                           let uu____2230 =
                             FStar_Extraction_ML_Code.string_of_mlexpr a_nm
                               a_let in
                           FStar_Util.print1 "Extracted action term: %s\n"
                             uu____2230
                         else ());
                        (let uu____2232 =
                           match a_let.FStar_Extraction_ML_Syntax.expr with
                           | FStar_Extraction_ML_Syntax.MLE_Let
                               ((uu____2241,uu____2242,mllb::[]),uu____2244)
                               ->
                               (match mllb.FStar_Extraction_ML_Syntax.mllb_tysc
                                with
                                | FStar_Pervasives_Native.Some tysc ->
                                    ((mllb.FStar_Extraction_ML_Syntax.mllb_def),
                                      tysc)
                                | FStar_Pervasives_Native.None  ->
                                    failwith "No type scheme")
                           | uu____2264 -> failwith "Impossible" in
                         match uu____2232 with
                         | (exp,tysc) ->
                             ((let uu____2276 =
                                 FStar_All.pipe_left
                                   (FStar_TypeChecker_Env.debug
                                      g1.FStar_Extraction_ML_UEnv.tcenv)
                                   (FStar_Options.Other "ExtractionReify") in
                               if uu____2276
                               then
                                 ((let uu____2278 =
                                     FStar_Extraction_ML_Code.string_of_mlty
                                       a_nm
                                       (FStar_Pervasives_Native.snd tysc) in
                                   FStar_Util.print1
                                     "Extracted action type: %s\n" uu____2278);
                                  FStar_List.iter
                                    (fun x  ->
                                       FStar_Util.print1 "and binders: %s\n"
                                         (FStar_Pervasives_Native.fst x))
                                    (FStar_Pervasives_Native.fst tysc))
                               else ());
                              extend_env g1 a_lid a_nm exp tysc))))) in
           let uu____2290 =
             let uu____2295 =
               extract_fv
                 (FStar_Pervasives_Native.snd
                    ed.FStar_Syntax_Syntax.return_repr) in
             match uu____2295 with
             | (return_tm,ty_sc) ->
                 let uu____2308 =
                   FStar_Extraction_ML_UEnv.monad_op_name ed "return" in
                 (match uu____2308 with
                  | (return_nm,return_lid) ->
                      extend_env g return_lid return_nm return_tm ty_sc) in
           (match uu____2290 with
            | (g1,return_decl) ->
                let uu____2327 =
                  let uu____2332 =
                    extract_fv
                      (FStar_Pervasives_Native.snd
                         ed.FStar_Syntax_Syntax.bind_repr) in
                  match uu____2332 with
                  | (bind_tm,ty_sc) ->
                      let uu____2345 =
                        FStar_Extraction_ML_UEnv.monad_op_name ed "bind" in
                      (match uu____2345 with
                       | (bind_nm,bind_lid) ->
                           extend_env g1 bind_lid bind_nm bind_tm ty_sc) in
                (match uu____2327 with
                 | (g2,bind_decl) ->
                     let uu____2364 =
                       FStar_Util.fold_map extract_action g2
                         ed.FStar_Syntax_Syntax.actions in
                     (match uu____2364 with
                      | (g3,actions) ->
                          (g3,
                            (FStar_List.append [return_decl; bind_decl]
                               actions)))))
       | FStar_Syntax_Syntax.Sig_new_effect uu____2385 -> (g, [])
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2389,t) when
           FStar_Extraction_ML_Term.is_arity g t ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let uu____2397 =
             let uu____2398 =
               FStar_All.pipe_right quals
                 (FStar_Util.for_some
                    (fun uu___156_2402  ->
                       match uu___156_2402 with
                       | FStar_Syntax_Syntax.Assumption  -> true
                       | uu____2403 -> false)) in
             Prims.op_Negation uu____2398 in
           if uu____2397
           then (g, [])
           else
             (let uu____2413 = FStar_Syntax_Util.arrow_formals t in
              match uu____2413 with
              | (bs,uu____2433) ->
                  let fv =
                    FStar_Syntax_Syntax.lid_as_fv lid
                      FStar_Syntax_Syntax.Delta_constant
                      FStar_Pervasives_Native.None in
                  let uu____2451 =
                    FStar_Syntax_Util.abs bs FStar_Syntax_Syntax.t_unit
                      FStar_Pervasives_Native.None in
                  extract_typ_abbrev g fv quals attrs uu____2451)
       | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____2453) when
           FStar_Extraction_ML_Term.is_arity g lb.FStar_Syntax_Syntax.lbtyp
           ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2469 =
             let uu____2478 =
               FStar_TypeChecker_Env.open_universes_in
                 g.FStar_Extraction_ML_UEnv.tcenv
                 lb.FStar_Syntax_Syntax.lbunivs
                 [lb.FStar_Syntax_Syntax.lbdef; lb.FStar_Syntax_Syntax.lbtyp] in
             match uu____2478 with
             | (tcenv,uu____2502,def_typ) ->
                 let uu____2508 = as_pair def_typ in (tcenv, uu____2508) in
           (match uu____2469 with
            | (tcenv,(lbdef,lbtyp)) ->
                let lbtyp1 =
                  FStar_TypeChecker_Normalize.normalize
                    [FStar_TypeChecker_Normalize.Beta;
                    FStar_TypeChecker_Normalize.UnfoldUntil
                      FStar_Syntax_Syntax.Delta_constant] tcenv lbtyp in
                let lbdef1 =
                  FStar_TypeChecker_Normalize.eta_expand_with_type tcenv
                    lbdef lbtyp1 in
                let uu____2532 =
                  FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                extract_typ_abbrev g uu____2532 quals
                  se.FStar_Syntax_Syntax.sigattrs lbdef1)
       | FStar_Syntax_Syntax.Sig_let (lbs,uu____2534) ->
           let attrs = se.FStar_Syntax_Syntax.sigattrs in
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let elet =
             FStar_Syntax_Syntax.mk
               (FStar_Syntax_Syntax.Tm_let
                  (lbs, FStar_Syntax_Util.exp_false_bool))
               FStar_Pervasives_Native.None se.FStar_Syntax_Syntax.sigrng in
           let tactic_registration_decl =
             let is_tactic_decl tac_lid h =
               match h.FStar_Syntax_Syntax.n with
               | FStar_Syntax_Syntax.Tm_uinst (h',uu____2561) ->
                   let uu____2566 =
                     let uu____2567 = FStar_Syntax_Subst.compress h' in
                     uu____2567.FStar_Syntax_Syntax.n in
                   (match uu____2566 with
                    | FStar_Syntax_Syntax.Tm_fvar fv when
                        FStar_Syntax_Syntax.fv_eq_lid fv
                          FStar_Parser_Const.tactic_lid
                        ->
                        let uu____2571 =
                          let uu____2572 =
                            FStar_Extraction_ML_Syntax.string_of_mlpath
                              g.FStar_Extraction_ML_UEnv.currentModule in
                          FStar_Util.starts_with uu____2572 "FStar.Tactics" in
                        Prims.op_Negation uu____2571
                    | uu____2573 -> false)
               | uu____2574 -> false in
             let mk_registration tac_lid assm_lid t bs =
               let h =
                 let uu____2601 =
                   let uu____2602 =
                     let uu____2603 =
                       FStar_Ident.lid_of_str
                         "FStar_Tactics_Native.register_tactic" in
                     FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2603 in
                   FStar_Extraction_ML_Syntax.MLE_Name uu____2602 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2601 in
               let lid_arg =
                 let uu____2605 =
                   let uu____2606 = FStar_Ident.string_of_lid assm_lid in
                   FStar_Extraction_ML_Syntax.MLC_String uu____2606 in
                 FStar_Extraction_ML_Syntax.MLE_Const uu____2605 in
               let tac_arity = FStar_List.length bs in
               let arity =
                 let uu____2613 =
                   let uu____2614 =
                     let uu____2615 =
                       FStar_Util.string_of_int
                         (tac_arity + (Prims.parse_int "1")) in
                     FStar_Ident.lid_of_str uu____2615 in
                   FStar_Extraction_ML_Syntax.mlpath_of_lident uu____2614 in
                 FStar_Extraction_ML_Syntax.MLE_Name uu____2613 in
               let tac_interpretation =
                 FStar_Extraction_ML_Util.mk_interpretation_fun tac_lid
                   lid_arg t bs in
               let app =
                 let uu____2624 =
                   let uu____2625 =
                     let uu____2632 =
                       FStar_List.map
                         (FStar_Extraction_ML_Syntax.with_ty
                            FStar_Extraction_ML_Syntax.MLTY_Top)
                         [lid_arg; arity; tac_interpretation] in
                     (h, uu____2632) in
                   FStar_Extraction_ML_Syntax.MLE_App uu____2625 in
                 FStar_All.pipe_left
                   (FStar_Extraction_ML_Syntax.with_ty
                      FStar_Extraction_ML_Syntax.MLTY_Top) uu____2624 in
               FStar_Extraction_ML_Syntax.MLM_Top app in
             match FStar_Pervasives_Native.snd lbs with
             | hd1::[] ->
                 let uu____2642 =
                   FStar_Syntax_Util.arrow_formals_comp
                     hd1.FStar_Syntax_Syntax.lbtyp in
                 (match uu____2642 with
                  | (bs,comp) ->
                      let t = FStar_Syntax_Util.comp_result comp in
                      let uu____2672 =
                        let uu____2673 = FStar_Syntax_Subst.compress t in
                        uu____2673.FStar_Syntax_Syntax.n in
                      (match uu____2672 with
                       | FStar_Syntax_Syntax.Tm_app (h,args) ->
                           let h1 = FStar_Syntax_Subst.compress h in
                           let tac_lid =
                             let uu____2702 =
                               let uu____2705 =
                                 FStar_Util.right
                                   hd1.FStar_Syntax_Syntax.lbname in
                               uu____2705.FStar_Syntax_Syntax.fv_name in
                             uu____2702.FStar_Syntax_Syntax.v in
                           let assm_lid =
                             let uu____2707 =
                               FStar_All.pipe_left FStar_Ident.id_of_text
                                 (Prims.strcat "__"
                                    (tac_lid.FStar_Ident.ident).FStar_Ident.idText) in
                             FStar_Ident.lid_of_ns_and_id
                               tac_lid.FStar_Ident.ns uu____2707 in
                           let uu____2708 = is_tactic_decl assm_lid h1 in
                           if uu____2708
                           then
                             let uu____2711 =
                               let uu____2712 =
                                 let uu____2713 = FStar_List.hd args in
                                 FStar_Pervasives_Native.fst uu____2713 in
                               mk_registration tac_lid assm_lid uu____2712 bs in
                             [uu____2711]
                           else []
                       | uu____2729 -> []))
             | uu____2730 -> [] in
           let uu____2733 = FStar_Extraction_ML_Term.term_as_mlexpr g elet in
           (match uu____2733 with
            | (ml_let,uu____2747,uu____2748) ->
                (match ml_let.FStar_Extraction_ML_Syntax.expr with
                 | FStar_Extraction_ML_Syntax.MLE_Let
                     ((flavor,uu____2756,bindings),uu____2758) ->
                     let uu____2771 =
                       FStar_List.fold_left2
                         (fun uu____2798  ->
                            fun ml_lb  ->
                              fun uu____2800  ->
                                match (uu____2798, uu____2800) with
                                | ((env,ml_lbs),{
                                                  FStar_Syntax_Syntax.lbname
                                                    = lbname;
                                                  FStar_Syntax_Syntax.lbunivs
                                                    = uu____2822;
                                                  FStar_Syntax_Syntax.lbtyp =
                                                    t;
                                                  FStar_Syntax_Syntax.lbeff =
                                                    uu____2824;
                                                  FStar_Syntax_Syntax.lbdef =
                                                    uu____2825;_})
                                    ->
                                    let lb_lid =
                                      let uu____2847 =
                                        let uu____2850 =
                                          FStar_Util.right lbname in
                                        uu____2850.FStar_Syntax_Syntax.fv_name in
                                      uu____2847.FStar_Syntax_Syntax.v in
                                    let uu____2851 =
                                      let uu____2856 =
                                        FStar_All.pipe_right quals
                                          (FStar_Util.for_some
                                             (fun uu___157_2861  ->
                                                match uu___157_2861 with
                                                | FStar_Syntax_Syntax.Projector
                                                    uu____2862 -> true
                                                | uu____2867 -> false)) in
                                      if uu____2856
                                      then
                                        let mname =
                                          let uu____2873 =
                                            mangle_projector_lid lb_lid in
                                          FStar_All.pipe_right uu____2873
                                            FStar_Extraction_ML_Syntax.mlpath_of_lident in
                                        let uu____2874 =
                                          let uu____2879 =
                                            FStar_Util.right lbname in
                                          let uu____2880 =
                                            FStar_Util.must
                                              ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                          FStar_Extraction_ML_UEnv.extend_fv'
                                            env uu____2879 mname uu____2880
                                            ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                            false in
                                        match uu____2874 with
                                        | (env1,uu____2886) ->
                                            (env1,
                                              (let uu___161_2888 = ml_lb in
                                               {
                                                 FStar_Extraction_ML_Syntax.mllb_name
                                                   =
                                                   ((FStar_Pervasives_Native.snd
                                                       mname),
                                                     (Prims.parse_int "0"));
                                                 FStar_Extraction_ML_Syntax.mllb_tysc
                                                   =
                                                   (uu___161_2888.FStar_Extraction_ML_Syntax.mllb_tysc);
                                                 FStar_Extraction_ML_Syntax.mllb_add_unit
                                                   =
                                                   (uu___161_2888.FStar_Extraction_ML_Syntax.mllb_add_unit);
                                                 FStar_Extraction_ML_Syntax.mllb_def
                                                   =
                                                   (uu___161_2888.FStar_Extraction_ML_Syntax.mllb_def);
                                                 FStar_Extraction_ML_Syntax.print_typ
                                                   =
                                                   (uu___161_2888.FStar_Extraction_ML_Syntax.print_typ)
                                               }))
                                      else
                                        (let uu____2892 =
                                           let uu____2893 =
                                             let uu____2898 =
                                               FStar_Util.must
                                                 ml_lb.FStar_Extraction_ML_Syntax.mllb_tysc in
                                             FStar_Extraction_ML_UEnv.extend_lb
                                               env lbname t uu____2898
                                               ml_lb.FStar_Extraction_ML_Syntax.mllb_add_unit
                                               false in
                                           FStar_All.pipe_left
                                             FStar_Pervasives_Native.fst
                                             uu____2893 in
                                         (uu____2892, ml_lb)) in
                                    (match uu____2851 with
                                     | (g1,ml_lb1) ->
                                         (g1, (ml_lb1 :: ml_lbs)))) (g, [])
                         bindings (FStar_Pervasives_Native.snd lbs) in
                     (match uu____2771 with
                      | (g1,ml_lbs') ->
                          let flags =
                            FStar_List.choose
                              (fun uu___158_2933  ->
                                 match uu___158_2933 with
                                 | FStar_Syntax_Syntax.Assumption  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Assumed
                                 | FStar_Syntax_Syntax.Private  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.Private
                                 | FStar_Syntax_Syntax.NoExtract  ->
                                     FStar_Pervasives_Native.Some
                                       FStar_Extraction_ML_Syntax.NoExtract
                                 | uu____2936 -> FStar_Pervasives_Native.None)
                              quals in
                          let flags' = extract_attrs attrs in
                          let uu____2940 =
                            let uu____2943 =
                              let uu____2946 =
                                let uu____2947 =
                                  FStar_Extraction_ML_Util.mlloc_of_range
                                    se.FStar_Syntax_Syntax.sigrng in
                                FStar_Extraction_ML_Syntax.MLM_Loc uu____2947 in
                              [uu____2946;
                              FStar_Extraction_ML_Syntax.MLM_Let
                                (flavor, (FStar_List.append flags flags'),
                                  (FStar_List.rev ml_lbs'))] in
                            FStar_List.append uu____2943
                              tactic_registration_decl in
                          (g1, uu____2940))
                 | uu____2954 ->
                     let uu____2955 =
                       let uu____2956 =
                         FStar_Extraction_ML_Code.string_of_mlexpr
                           g.FStar_Extraction_ML_UEnv.currentModule ml_let in
                       FStar_Util.format1
                         "Impossible: Translated a let to a non-let: %s"
                         uu____2956 in
                     failwith uu____2955))
       | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____2964,t) ->
           let quals = se.FStar_Syntax_Syntax.sigquals in
           let uu____2969 =
             FStar_All.pipe_right quals
               (FStar_List.contains FStar_Syntax_Syntax.Assumption) in
           if uu____2969
           then
             let always_fail =
               let imp =
                 let uu____2980 = FStar_Syntax_Util.arrow_formals t in
                 match uu____2980 with
                 | ([],t1) ->
                     let b =
                       let uu____3009 =
                         FStar_Syntax_Syntax.gen_bv "_"
                           FStar_Pervasives_Native.None t1 in
                       FStar_All.pipe_left FStar_Syntax_Syntax.mk_binder
                         uu____3009 in
                     let uu____3010 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs [b] uu____3010
                       FStar_Pervasives_Native.None
                 | (bs,t1) ->
                     let uu____3029 = fail_exp lid t1 in
                     FStar_Syntax_Util.abs bs uu____3029
                       FStar_Pervasives_Native.None in
               let uu___162_3030 = se in
               let uu____3031 =
                 let uu____3032 =
                   let uu____3039 =
                     let uu____3046 =
                       let uu____3049 =
                         let uu____3050 =
                           let uu____3055 =
                             FStar_Syntax_Syntax.lid_as_fv lid
                               FStar_Syntax_Syntax.Delta_constant
                               FStar_Pervasives_Native.None in
                           FStar_Util.Inr uu____3055 in
                         {
                           FStar_Syntax_Syntax.lbname = uu____3050;
                           FStar_Syntax_Syntax.lbunivs = [];
                           FStar_Syntax_Syntax.lbtyp = t;
                           FStar_Syntax_Syntax.lbeff =
                             FStar_Parser_Const.effect_ML_lid;
                           FStar_Syntax_Syntax.lbdef = imp
                         } in
                       [uu____3049] in
                     (false, uu____3046) in
                   (uu____3039, []) in
                 FStar_Syntax_Syntax.Sig_let uu____3032 in
               {
                 FStar_Syntax_Syntax.sigel = uu____3031;
                 FStar_Syntax_Syntax.sigrng =
                   (uu___162_3030.FStar_Syntax_Syntax.sigrng);
                 FStar_Syntax_Syntax.sigquals =
                   (uu___162_3030.FStar_Syntax_Syntax.sigquals);
                 FStar_Syntax_Syntax.sigmeta =
                   (uu___162_3030.FStar_Syntax_Syntax.sigmeta);
                 FStar_Syntax_Syntax.sigattrs =
                   (uu___162_3030.FStar_Syntax_Syntax.sigattrs)
               } in
             let uu____3066 = extract_sig g always_fail in
             (match uu____3066 with
              | (g1,mlm) ->
                  let uu____3085 =
                    FStar_Util.find_map quals
                      (fun uu___159_3090  ->
                         match uu___159_3090 with
                         | FStar_Syntax_Syntax.Discriminator l ->
                             FStar_Pervasives_Native.Some l
                         | uu____3094 -> FStar_Pervasives_Native.None) in
                  (match uu____3085 with
                   | FStar_Pervasives_Native.Some l ->
                       let uu____3102 =
                         let uu____3105 =
                           let uu____3106 =
                             FStar_Extraction_ML_Util.mlloc_of_range
                               se.FStar_Syntax_Syntax.sigrng in
                           FStar_Extraction_ML_Syntax.MLM_Loc uu____3106 in
                         let uu____3107 =
                           let uu____3110 =
                             FStar_Extraction_ML_Term.ind_discriminator_body
                               g1 lid l in
                           [uu____3110] in
                         uu____3105 :: uu____3107 in
                       (g1, uu____3102)
                   | uu____3113 ->
                       let uu____3116 =
                         FStar_Util.find_map quals
                           (fun uu___160_3122  ->
                              match uu___160_3122 with
                              | FStar_Syntax_Syntax.Projector (l,uu____3126)
                                  -> FStar_Pervasives_Native.Some l
                              | uu____3127 -> FStar_Pervasives_Native.None) in
                       (match uu____3116 with
                        | FStar_Pervasives_Native.Some uu____3134 -> (g1, [])
                        | uu____3137 -> (g1, mlm))))
           else (g, [])
       | FStar_Syntax_Syntax.Sig_main e ->
           let uu____3146 = FStar_Extraction_ML_Term.term_as_mlexpr g e in
           (match uu____3146 with
            | (ml_main,uu____3160,uu____3161) ->
                let uu____3162 =
                  let uu____3165 =
                    let uu____3166 =
                      FStar_Extraction_ML_Util.mlloc_of_range
                        se.FStar_Syntax_Syntax.sigrng in
                    FStar_Extraction_ML_Syntax.MLM_Loc uu____3166 in
                  [uu____3165; FStar_Extraction_ML_Syntax.MLM_Top ml_main] in
                (g, uu____3162))
       | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____3169 ->
           failwith "impossible -- removed by tc.fs"
       | FStar_Syntax_Syntax.Sig_assume uu____3176 -> (g, [])
       | FStar_Syntax_Syntax.Sig_sub_effect uu____3185 -> (g, [])
       | FStar_Syntax_Syntax.Sig_effect_abbrev uu____3188 -> (g, [])
       | FStar_Syntax_Syntax.Sig_pragma p ->
           (if p = FStar_Syntax_Syntax.LightOff
            then FStar_Options.set_ml_ish ()
            else ();
            (g, [])))
let extract_iface:
  FStar_Extraction_ML_UEnv.env -> FStar_Syntax_Syntax.modul -> env_t =
  fun g  ->
    fun m  ->
      let uu____3216 =
        FStar_Util.fold_map extract_sig g m.FStar_Syntax_Syntax.declarations in
      FStar_All.pipe_right uu____3216 FStar_Pervasives_Native.fst
let extract:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Syntax_Syntax.modul ->
      (FStar_Extraction_ML_UEnv.env,FStar_Extraction_ML_Syntax.mllib
                                      Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun g  ->
    fun m  ->
      FStar_Syntax_Syntax.reset_gensym ();
      (let uu____3261 = FStar_Options.debug_any () in
       if uu____3261
       then
         let uu____3262 =
           FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
         FStar_Util.print1 "Extracting module %s\n" uu____3262
       else ());
      (let uu____3264 = FStar_Options.restore_cmd_line_options true in
       let name =
         FStar_Extraction_ML_Syntax.mlpath_of_lident
           m.FStar_Syntax_Syntax.name in
       let g1 =
         let uu___163_3267 = g in
         let uu____3268 =
           FStar_TypeChecker_Env.set_current_module
             g.FStar_Extraction_ML_UEnv.tcenv m.FStar_Syntax_Syntax.name in
         {
           FStar_Extraction_ML_UEnv.tcenv = uu____3268;
           FStar_Extraction_ML_UEnv.gamma =
             (uu___163_3267.FStar_Extraction_ML_UEnv.gamma);
           FStar_Extraction_ML_UEnv.tydefs =
             (uu___163_3267.FStar_Extraction_ML_UEnv.tydefs);
           FStar_Extraction_ML_UEnv.type_names =
             (uu___163_3267.FStar_Extraction_ML_UEnv.type_names);
           FStar_Extraction_ML_UEnv.currentModule = name
         } in
       let uu____3269 =
         FStar_Util.fold_map extract_sig g1
           m.FStar_Syntax_Syntax.declarations in
       match uu____3269 with
       | (g2,sigs) ->
           let mlm = FStar_List.flatten sigs in
           let is_kremlin =
             let uu____3298 = FStar_Options.codegen () in
             match uu____3298 with
             | FStar_Pervasives_Native.Some "Kremlin" -> true
             | uu____3301 -> false in
           let uu____3304 =
             (((m.FStar_Syntax_Syntax.name).FStar_Ident.str <> "Prims") &&
                (is_kremlin ||
                   (Prims.op_Negation m.FStar_Syntax_Syntax.is_interface)))
               &&
               (FStar_Options.should_extract
                  (m.FStar_Syntax_Syntax.name).FStar_Ident.str) in
           if uu____3304
           then
             ((let uu____3312 =
                 FStar_Syntax_Print.lid_to_string m.FStar_Syntax_Syntax.name in
               FStar_Util.print1 "Extracted module %s\n" uu____3312);
              (g2,
                [FStar_Extraction_ML_Syntax.MLLib
                   [(name, (FStar_Pervasives_Native.Some ([], mlm)),
                      (FStar_Extraction_ML_Syntax.MLLib []))]]))
           else (g2, []))