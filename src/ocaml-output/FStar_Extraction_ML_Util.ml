open Prims
let pruneNones:
  'a . 'a FStar_Pervasives_Native.option Prims.list -> 'a Prims.list =
  fun l  ->
    FStar_List.fold_right
      (fun x  ->
         fun ll  ->
           match x with
           | FStar_Pervasives_Native.Some xs -> xs :: ll
           | FStar_Pervasives_Native.None  -> ll) l []
let mk_range_mle: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "mk_range"))
let mlconst_of_const':
  FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant =
  fun sctt  ->
    match sctt with
    | FStar_Const.Const_effect  -> failwith "Unsupported constant"
    | FStar_Const.Const_range uu____42 -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_unit  -> FStar_Extraction_ML_Syntax.MLC_Unit
    | FStar_Const.Const_char c -> FStar_Extraction_ML_Syntax.MLC_Char c
    | FStar_Const.Const_int (s,i) ->
        FStar_Extraction_ML_Syntax.MLC_Int (s, i)
    | FStar_Const.Const_bool b -> FStar_Extraction_ML_Syntax.MLC_Bool b
    | FStar_Const.Const_float d -> FStar_Extraction_ML_Syntax.MLC_Float d
    | FStar_Const.Const_bytearray (bytes,uu____67) ->
        FStar_Extraction_ML_Syntax.MLC_Bytes bytes
    | FStar_Const.Const_string (s,uu____73) ->
        FStar_Extraction_ML_Syntax.MLC_String s
    | FStar_Const.Const_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_set_range_of  ->
        failwith "Unhandled constant: range_of/set_range_of"
    | FStar_Const.Const_reify  ->
        failwith "Unhandled constant: reify/reflect"
    | FStar_Const.Const_reflect uu____74 ->
        failwith "Unhandled constant: reify/reflect"
let mlconst_of_const:
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlconstant
  =
  fun p  ->
    fun c  ->
      try mlconst_of_const' c
      with
      | uu____89 ->
          let uu____90 =
            let uu____91 = FStar_Range.string_of_range p in
            let uu____92 = FStar_Syntax_Print.const_to_string c in
            FStar_Util.format2 "(%s) Failed to translate constant %s "
              uu____91 uu____92 in
          failwith uu____90
let mlexpr_of_const:
  FStar_Range.range ->
    FStar_Const.sconst -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun p  ->
    fun c  ->
      match c with
      | FStar_Const.Const_range r ->
          let cint i =
            let uu____106 =
              let uu____107 =
                let uu____108 =
                  let uu____119 = FStar_Util.string_of_int i in
                  (uu____119, FStar_Pervasives_Native.None) in
                FStar_Extraction_ML_Syntax.MLC_Int uu____108 in
              FStar_All.pipe_right uu____107
                (fun _0_42  -> FStar_Extraction_ML_Syntax.MLE_Const _0_42) in
            FStar_All.pipe_right uu____106
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.ml_int_ty) in
          let cstr s =
            let uu____134 =
              FStar_All.pipe_right (FStar_Extraction_ML_Syntax.MLC_String s)
                (fun _0_43  -> FStar_Extraction_ML_Syntax.MLE_Const _0_43) in
            FStar_All.pipe_right uu____134
              (FStar_Extraction_ML_Syntax.with_ty
                 FStar_Extraction_ML_Syntax.ml_string_ty) in
          let uu____135 =
            let uu____142 =
              let uu____145 =
                let uu____146 = FStar_Range.file_of_range r in
                FStar_All.pipe_right uu____146 cstr in
              let uu____147 =
                let uu____150 =
                  let uu____151 =
                    let uu____152 = FStar_Range.start_of_range r in
                    FStar_All.pipe_right uu____152 FStar_Range.line_of_pos in
                  FStar_All.pipe_right uu____151 cint in
                let uu____153 =
                  let uu____156 =
                    let uu____157 =
                      let uu____158 = FStar_Range.start_of_range r in
                      FStar_All.pipe_right uu____158 FStar_Range.col_of_pos in
                    FStar_All.pipe_right uu____157 cint in
                  let uu____159 =
                    let uu____162 =
                      let uu____163 =
                        let uu____164 = FStar_Range.end_of_range r in
                        FStar_All.pipe_right uu____164
                          FStar_Range.line_of_pos in
                      FStar_All.pipe_right uu____163 cint in
                    let uu____165 =
                      let uu____168 =
                        let uu____169 =
                          let uu____170 = FStar_Range.end_of_range r in
                          FStar_All.pipe_right uu____170
                            FStar_Range.col_of_pos in
                        FStar_All.pipe_right uu____169 cint in
                      [uu____168] in
                    uu____162 :: uu____165 in
                  uu____156 :: uu____159 in
                uu____150 :: uu____153 in
              uu____145 :: uu____147 in
            (mk_range_mle, uu____142) in
          FStar_Extraction_ML_Syntax.MLE_App uu____135
      | uu____173 ->
          let uu____174 = mlconst_of_const p c in
          FStar_Extraction_ML_Syntax.MLE_Const uu____174
let rec subst_aux:
  (FStar_Extraction_ML_Syntax.mlident,FStar_Extraction_ML_Syntax.mlty)
    FStar_Pervasives_Native.tuple2 Prims.list ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun subst1  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Var x ->
          let uu____196 =
            FStar_Util.find_opt
              (fun uu____210  ->
                 match uu____210 with | (y,uu____216) -> y = x) subst1 in
          (match uu____196 with
           | FStar_Pervasives_Native.Some ts ->
               FStar_Pervasives_Native.snd ts
           | FStar_Pervasives_Native.None  -> t)
      | FStar_Extraction_ML_Syntax.MLTY_Fun (t1,f,t2) ->
          let uu____233 =
            let uu____240 = subst_aux subst1 t1 in
            let uu____241 = subst_aux subst1 t2 in (uu____240, f, uu____241) in
          FStar_Extraction_ML_Syntax.MLTY_Fun uu____233
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,path) ->
          let uu____248 =
            let uu____255 = FStar_List.map (subst_aux subst1) args in
            (uu____255, path) in
          FStar_Extraction_ML_Syntax.MLTY_Named uu____248
      | FStar_Extraction_ML_Syntax.MLTY_Tuple ts ->
          let uu____263 = FStar_List.map (subst_aux subst1) ts in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____263
      | FStar_Extraction_ML_Syntax.MLTY_Top  ->
          FStar_Extraction_ML_Syntax.MLTY_Top
let try_subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun uu____276  ->
    fun args  ->
      match uu____276 with
      | (formals,t) ->
          if (FStar_List.length formals) <> (FStar_List.length args)
          then FStar_Pervasives_Native.None
          else
            (let uu____287 =
               let uu____288 = FStar_List.zip formals args in
               subst_aux uu____288 t in
             FStar_Pervasives_Native.Some uu____287)
let subst:
  FStar_Extraction_ML_Syntax.mltyscheme ->
    FStar_Extraction_ML_Syntax.mlty Prims.list ->
      FStar_Extraction_ML_Syntax.mlty
  =
  fun ts  ->
    fun args  ->
      let uu____307 = try_subst ts args in
      match uu____307 with
      | FStar_Pervasives_Native.None  ->
          failwith
            "Substitution must be fully applied (see GitHub issue #490)"
      | FStar_Pervasives_Native.Some t -> t
let udelta_unfold:
  FStar_Extraction_ML_UEnv.env ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option
  =
  fun g  ->
    fun uu___147_320  ->
      match uu___147_320 with
      | FStar_Extraction_ML_Syntax.MLTY_Named (args,n1) ->
          let uu____329 = FStar_Extraction_ML_UEnv.lookup_ty_const g n1 in
          (match uu____329 with
           | FStar_Pervasives_Native.Some ts ->
               let uu____335 = try_subst ts args in
               (match uu____335 with
                | FStar_Pervasives_Native.None  ->
                    let uu____340 =
                      let uu____341 =
                        FStar_Extraction_ML_Syntax.string_of_mlpath n1 in
                      let uu____342 =
                        FStar_Util.string_of_int (FStar_List.length args) in
                      let uu____343 =
                        FStar_Util.string_of_int
                          (FStar_List.length (FStar_Pervasives_Native.fst ts)) in
                      FStar_Util.format3
                        "Substitution must be fully applied; got an application of %s with %s args whereas %s were expected (see GitHub issue #490)"
                        uu____341 uu____342 uu____343 in
                    failwith uu____340
                | FStar_Pervasives_Native.Some r ->
                    FStar_Pervasives_Native.Some r)
           | uu____347 -> FStar_Pervasives_Native.None)
      | uu____350 -> FStar_Pervasives_Native.None
let eff_leq:
  FStar_Extraction_ML_Syntax.e_tag ->
    FStar_Extraction_ML_Syntax.e_tag -> Prims.bool
  =
  fun f  ->
    fun f'  ->
      match (f, f') with
      | (FStar_Extraction_ML_Syntax.E_PURE ,uu____359) -> true
      | (FStar_Extraction_ML_Syntax.E_GHOST
         ,FStar_Extraction_ML_Syntax.E_GHOST ) -> true
      | (FStar_Extraction_ML_Syntax.E_IMPURE
         ,FStar_Extraction_ML_Syntax.E_IMPURE ) -> true
      | uu____360 -> false
let eff_to_string: FStar_Extraction_ML_Syntax.e_tag -> Prims.string =
  fun uu___148_368  ->
    match uu___148_368 with
    | FStar_Extraction_ML_Syntax.E_PURE  -> "Pure"
    | FStar_Extraction_ML_Syntax.E_GHOST  -> "Ghost"
    | FStar_Extraction_ML_Syntax.E_IMPURE  -> "Impure"
let join:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag ->
      FStar_Extraction_ML_Syntax.e_tag -> FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun f  ->
      fun f'  ->
        match (f, f') with
        | (FStar_Extraction_ML_Syntax.E_IMPURE
           ,FStar_Extraction_ML_Syntax.E_PURE ) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.E_IMPURE ) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_IMPURE
           ,FStar_Extraction_ML_Syntax.E_IMPURE ) ->
            FStar_Extraction_ML_Syntax.E_IMPURE
        | (FStar_Extraction_ML_Syntax.E_GHOST
           ,FStar_Extraction_ML_Syntax.E_GHOST ) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.E_GHOST ) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_GHOST
           ,FStar_Extraction_ML_Syntax.E_PURE ) ->
            FStar_Extraction_ML_Syntax.E_GHOST
        | (FStar_Extraction_ML_Syntax.E_PURE
           ,FStar_Extraction_ML_Syntax.E_PURE ) ->
            FStar_Extraction_ML_Syntax.E_PURE
        | uu____381 ->
            let uu____386 =
              let uu____387 = FStar_Range.string_of_range r in
              FStar_Util.format3
                "Impossible (%s): Inconsistent effects %s and %s" uu____387
                (eff_to_string f) (eff_to_string f') in
            failwith uu____386
let join_l:
  FStar_Range.range ->
    FStar_Extraction_ML_Syntax.e_tag Prims.list ->
      FStar_Extraction_ML_Syntax.e_tag
  =
  fun r  ->
    fun fs  ->
      FStar_List.fold_left (join r) FStar_Extraction_ML_Syntax.E_PURE fs
let mk_ty_fun:
  'Auu____406 .
    Prims.unit ->
      ('Auu____406,FStar_Extraction_ML_Syntax.mlty)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun uu____417  ->
    FStar_List.fold_right
      (fun uu____426  ->
         fun t  ->
           match uu____426 with
           | (uu____432,t0) ->
               FStar_Extraction_ML_Syntax.MLTY_Fun
                 (t0, FStar_Extraction_ML_Syntax.E_PURE, t))
type unfold_t =
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty FStar_Pervasives_Native.option[@@deriving
                                                                    show]
let rec type_leq_c:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlty ->
        FStar_Extraction_ML_Syntax.mlty ->
          (Prims.bool,FStar_Extraction_ML_Syntax.mlexpr
                        FStar_Pervasives_Native.option)
            FStar_Pervasives_Native.tuple2
  =
  fun unfold_ty  ->
    fun e  ->
      fun t  ->
        fun t'  ->
          match (t, t') with
          | (FStar_Extraction_ML_Syntax.MLTY_Var
             x,FStar_Extraction_ML_Syntax.MLTY_Var y) ->
              if x = y
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Fun
             (t1,f,t2),FStar_Extraction_ML_Syntax.MLTY_Fun (t1',f',t2')) ->
              let mk_fun xs body =
                match xs with
                | [] -> body
                | uu____519 ->
                    let e1 =
                      match body.FStar_Extraction_ML_Syntax.expr with
                      | FStar_Extraction_ML_Syntax.MLE_Fun (ys,body1) ->
                          FStar_Extraction_ML_Syntax.MLE_Fun
                            ((FStar_List.append xs ys), body1)
                      | uu____551 ->
                          FStar_Extraction_ML_Syntax.MLE_Fun (xs, body) in
                    let uu____558 =
                      (mk_ty_fun ()) xs body.FStar_Extraction_ML_Syntax.mlty in
                    FStar_Extraction_ML_Syntax.with_ty uu____558 e1 in
              (match e with
               | FStar_Pervasives_Native.Some
                   {
                     FStar_Extraction_ML_Syntax.expr =
                       FStar_Extraction_ML_Syntax.MLE_Fun (x::xs,body);
                     FStar_Extraction_ML_Syntax.mlty = uu____568;
                     FStar_Extraction_ML_Syntax.loc = uu____569;_}
                   ->
                   let uu____590 =
                     (type_leq unfold_ty t1' t1) && (eff_leq f f') in
                   if uu____590
                   then
                     (if
                        (f = FStar_Extraction_ML_Syntax.E_PURE) &&
                          (f' = FStar_Extraction_ML_Syntax.E_GHOST)
                      then
                        let uu____606 = type_leq unfold_ty t2 t2' in
                        (if uu____606
                         then
                           let body1 =
                             let uu____617 =
                               type_leq unfold_ty t2
                                 FStar_Extraction_ML_Syntax.ml_unit_ty in
                             if uu____617
                             then FStar_Extraction_ML_Syntax.ml_unit
                             else
                               FStar_All.pipe_left
                                 (FStar_Extraction_ML_Syntax.with_ty t2')
                                 (FStar_Extraction_ML_Syntax.MLE_Coerce
                                    (FStar_Extraction_ML_Syntax.ml_unit,
                                      FStar_Extraction_ML_Syntax.ml_unit_ty,
                                      t2')) in
                           let uu____622 =
                             let uu____625 =
                               let uu____626 =
                                 let uu____629 =
                                   (mk_ty_fun ()) [x]
                                     body1.FStar_Extraction_ML_Syntax.mlty in
                                 FStar_Extraction_ML_Syntax.with_ty uu____629 in
                               FStar_All.pipe_left uu____626
                                 (FStar_Extraction_ML_Syntax.MLE_Fun
                                    ([x], body1)) in
                             FStar_Pervasives_Native.Some uu____625 in
                           (true, uu____622)
                         else (false, FStar_Pervasives_Native.None))
                      else
                        (let uu____658 =
                           let uu____665 =
                             let uu____668 = mk_fun xs body in
                             FStar_All.pipe_left
                               (fun _0_44  ->
                                  FStar_Pervasives_Native.Some _0_44)
                               uu____668 in
                           type_leq_c unfold_ty uu____665 t2 t2' in
                         match uu____658 with
                         | (ok,body1) ->
                             let res =
                               match body1 with
                               | FStar_Pervasives_Native.Some body2 ->
                                   let uu____692 = mk_fun [x] body2 in
                                   FStar_Pervasives_Native.Some uu____692
                               | uu____701 -> FStar_Pervasives_Native.None in
                             (ok, res)))
                   else (false, FStar_Pervasives_Native.None)
               | uu____709 ->
                   let uu____712 =
                     ((type_leq unfold_ty t1' t1) && (eff_leq f f')) &&
                       (type_leq unfold_ty t2 t2') in
                   if uu____712
                   then (true, e)
                   else (false, FStar_Pervasives_Native.None))
          | (FStar_Extraction_ML_Syntax.MLTY_Named
             (args,path),FStar_Extraction_ML_Syntax.MLTY_Named (args',path'))
              ->
              if path = path'
              then
                let uu____748 =
                  FStar_List.forall2 (type_leq unfold_ty) args args' in
                (if uu____748
                 then (true, e)
                 else (false, FStar_Pervasives_Native.None))
              else
                (let uu____764 = unfold_ty t in
                 match uu____764 with
                 | FStar_Pervasives_Native.Some t1 ->
                     type_leq_c unfold_ty e t1 t'
                 | FStar_Pervasives_Native.None  ->
                     let uu____778 = unfold_ty t' in
                     (match uu____778 with
                      | FStar_Pervasives_Native.None  ->
                          (false, FStar_Pervasives_Native.None)
                      | FStar_Pervasives_Native.Some t'1 ->
                          type_leq_c unfold_ty e t t'1))
          | (FStar_Extraction_ML_Syntax.MLTY_Tuple
             ts,FStar_Extraction_ML_Syntax.MLTY_Tuple ts') ->
              let uu____800 = FStar_List.forall2 (type_leq unfold_ty) ts ts' in
              if uu____800
              then (true, e)
              else (false, FStar_Pervasives_Native.None)
          | (FStar_Extraction_ML_Syntax.MLTY_Top
             ,FStar_Extraction_ML_Syntax.MLTY_Top ) -> (true, e)
          | (FStar_Extraction_ML_Syntax.MLTY_Named uu____817,uu____818) ->
              let uu____825 = unfold_ty t in
              (match uu____825 with
               | FStar_Pervasives_Native.Some t1 ->
                   type_leq_c unfold_ty e t1 t'
               | uu____839 -> (false, FStar_Pervasives_Native.None))
          | (uu____844,FStar_Extraction_ML_Syntax.MLTY_Named uu____845) ->
              let uu____852 = unfold_ty t' in
              (match uu____852 with
               | FStar_Pervasives_Native.Some t'1 ->
                   type_leq_c unfold_ty e t t'1
               | uu____866 -> (false, FStar_Pervasives_Native.None))
          | uu____871 -> (false, FStar_Pervasives_Native.None)
and type_leq:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty ->
      FStar_Extraction_ML_Syntax.mlty -> Prims.bool
  =
  fun g  ->
    fun t1  ->
      fun t2  ->
        let uu____882 = type_leq_c g FStar_Pervasives_Native.None t1 t2 in
        FStar_All.pipe_right uu____882 FStar_Pervasives_Native.fst
let is_type_abstraction:
  'Auu____908 'Auu____909 'Auu____910 .
    (('Auu____910,'Auu____909) FStar_Util.either,'Auu____908)
      FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun uu___149_924  ->
    match uu___149_924 with
    | (FStar_Util.Inl uu____935,uu____936)::uu____937 -> true
    | uu____960 -> false
let is_xtuple:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____982  ->
    match uu____982 with
    | (ns,n1) ->
        let uu____997 =
          let uu____998 = FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_datacon_string uu____998 in
        if uu____997
        then
          let uu____1001 =
            let uu____1002 = FStar_Util.char_at n1 (Prims.parse_int "7") in
            FStar_Util.int_of_char uu____1002 in
          FStar_Pervasives_Native.Some uu____1001
        else FStar_Pervasives_Native.None
let resugar_exp:
  FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr =
  fun e  ->
    match e.FStar_Extraction_ML_Syntax.expr with
    | FStar_Extraction_ML_Syntax.MLE_CTor (mlp,args) ->
        let uu____1014 = is_xtuple mlp in
        (match uu____1014 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_All.pipe_left
               (FStar_Extraction_ML_Syntax.with_ty
                  e.FStar_Extraction_ML_Syntax.mlty)
               (FStar_Extraction_ML_Syntax.MLE_Tuple args)
         | uu____1018 -> e)
    | uu____1021 -> e
let record_field_path:
  FStar_Ident.lident Prims.list -> Prims.string Prims.list =
  fun uu___150_1029  ->
    match uu___150_1029 with
    | f::uu____1035 ->
        let uu____1038 = FStar_Util.prefix f.FStar_Ident.ns in
        (match uu____1038 with
         | (ns,uu____1048) ->
             FStar_All.pipe_right ns
               (FStar_List.map (fun id  -> id.FStar_Ident.idText)))
    | uu____1059 -> failwith "impos"
let record_fields:
  'Auu____1070 .
    FStar_Ident.lident Prims.list ->
      'Auu____1070 Prims.list ->
        (Prims.string,'Auu____1070) FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun fs  ->
    fun vs  ->
      FStar_List.map2
        (fun f  -> fun e  -> (((f.FStar_Ident.ident).FStar_Ident.idText), e))
        fs vs
let is_xtuple_ty:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.int FStar_Pervasives_Native.option
  =
  fun uu____1112  ->
    match uu____1112 with
    | (ns,n1) ->
        let uu____1127 =
          let uu____1128 =
            FStar_Util.concat_l "." (FStar_List.append ns [n1]) in
          FStar_Parser_Const.is_tuple_constructor_string uu____1128 in
        if uu____1127
        then
          let uu____1131 =
            let uu____1132 = FStar_Util.char_at n1 (Prims.parse_int "5") in
            FStar_Util.int_of_char uu____1132 in
          FStar_Pervasives_Native.Some uu____1131
        else FStar_Pervasives_Native.None
let resugar_mlty:
  FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Named (args,mlp) ->
        let uu____1144 = is_xtuple_ty mlp in
        (match uu____1144 with
         | FStar_Pervasives_Native.Some n1 ->
             FStar_Extraction_ML_Syntax.MLTY_Tuple args
         | uu____1148 -> t)
    | uu____1151 -> t
let flatten_ns: Prims.string Prims.list -> Prims.string =
  fun ns  ->
    let uu____1160 = FStar_Options.codegen_fsharp () in
    if uu____1160
    then FStar_String.concat "." ns
    else FStar_String.concat "_" ns
let flatten_mlpath:
  (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2 ->
    Prims.string
  =
  fun uu____1171  ->
    match uu____1171 with
    | (ns,n1) ->
        let uu____1184 = FStar_Options.codegen_fsharp () in
        if uu____1184
        then FStar_String.concat "." (FStar_List.append ns [n1])
        else FStar_String.concat "_" (FStar_List.append ns [n1])
let mlpath_of_lid:
  FStar_Ident.lident ->
    (Prims.string Prims.list,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    let uu____1196 =
      FStar_All.pipe_right l.FStar_Ident.ns
        (FStar_List.map (fun i  -> i.FStar_Ident.idText)) in
    (uu____1196, ((l.FStar_Ident.ident).FStar_Ident.idText))
let rec erasableType:
  unfold_t -> FStar_Extraction_ML_Syntax.mlty -> Prims.bool =
  fun unfold_ty  ->
    fun t  ->
      if FStar_Extraction_ML_UEnv.erasableTypeNoDelta t
      then true
      else
        (let uu____1219 = unfold_ty t in
         match uu____1219 with
         | FStar_Pervasives_Native.Some t1 -> erasableType unfold_ty t1
         | FStar_Pervasives_Native.None  -> false)
let rec eraseTypeDeep:
  unfold_t ->
    FStar_Extraction_ML_Syntax.mlty -> FStar_Extraction_ML_Syntax.mlty
  =
  fun unfold_ty  ->
    fun t  ->
      match t with
      | FStar_Extraction_ML_Syntax.MLTY_Fun (tyd,etag,tycd) ->
          if etag = FStar_Extraction_ML_Syntax.E_PURE
          then
            let uu____1241 =
              let uu____1248 = eraseTypeDeep unfold_ty tyd in
              let uu____1252 = eraseTypeDeep unfold_ty tycd in
              (uu____1248, etag, uu____1252) in
            FStar_Extraction_ML_Syntax.MLTY_Fun uu____1241
          else t
      | FStar_Extraction_ML_Syntax.MLTY_Named (lty,mlp) ->
          let uu____1263 = erasableType unfold_ty t in
          if uu____1263
          then FStar_Extraction_ML_UEnv.erasedContent
          else
            (let uu____1268 =
               let uu____1275 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
               (uu____1275, mlp) in
             FStar_Extraction_ML_Syntax.MLTY_Named uu____1268)
      | FStar_Extraction_ML_Syntax.MLTY_Tuple lty ->
          let uu____1286 = FStar_List.map (eraseTypeDeep unfold_ty) lty in
          FStar_Extraction_ML_Syntax.MLTY_Tuple uu____1286
      | uu____1292 -> t
let prims_op_equality: FStar_Extraction_ML_Syntax.mlexpr =
  FStar_All.pipe_left
    (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_Equality"))
let prims_op_amp_amp: FStar_Extraction_ML_Syntax.mlexpr =
  let uu____1295 =
    let uu____1298 =
      (mk_ty_fun ())
        [("x", FStar_Extraction_ML_Syntax.ml_bool_ty);
        ("y", FStar_Extraction_ML_Syntax.ml_bool_ty)]
        FStar_Extraction_ML_Syntax.ml_bool_ty in
    FStar_Extraction_ML_Syntax.with_ty uu____1298 in
  FStar_All.pipe_left uu____1295
    (FStar_Extraction_ML_Syntax.MLE_Name (["Prims"], "op_AmpAmp"))
let conjoin:
  FStar_Extraction_ML_Syntax.mlexpr ->
    FStar_Extraction_ML_Syntax.mlexpr -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun e1  ->
    fun e2  ->
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.ml_bool_ty)
        (FStar_Extraction_ML_Syntax.MLE_App (prims_op_amp_amp, [e1; e2]))
let conjoin_opt:
  FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
    FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option ->
      FStar_Extraction_ML_Syntax.mlexpr FStar_Pervasives_Native.option
  =
  fun e1  ->
    fun e2  ->
      match (e1, e2) with
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.None
      | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.None ) ->
          FStar_Pervasives_Native.Some x
      | (FStar_Pervasives_Native.None ,FStar_Pervasives_Native.Some x) ->
          FStar_Pervasives_Native.Some x
      | (FStar_Pervasives_Native.Some x,FStar_Pervasives_Native.Some y) ->
          let uu____1367 = conjoin x y in
          FStar_Pervasives_Native.Some uu____1367
let mlloc_of_range:
  FStar_Range.range ->
    (Prims.int,Prims.string) FStar_Pervasives_Native.tuple2
  =
  fun r  ->
    let pos = FStar_Range.start_of_range r in
    let line = FStar_Range.line_of_pos pos in
    let uu____1378 = FStar_Range.file_of_range r in (line, uu____1378)
let rec doms_and_cod:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1396,b) ->
        let uu____1398 = doms_and_cod b in
        (match uu____1398 with | (ds,c) -> ((a :: ds), c))
    | uu____1419 -> ([], t)
let argTypes:
  FStar_Extraction_ML_Syntax.mlty ->
    FStar_Extraction_ML_Syntax.mlty Prims.list
  =
  fun t  ->
    let uu____1430 = doms_and_cod t in FStar_Pervasives_Native.fst uu____1430
let rec uncurry_mlty_fun:
  FStar_Extraction_ML_Syntax.mlty ->
    (FStar_Extraction_ML_Syntax.mlty Prims.list,FStar_Extraction_ML_Syntax.mlty)
      FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    match t with
    | FStar_Extraction_ML_Syntax.MLTY_Fun (a,uu____1456,b) ->
        let uu____1458 = uncurry_mlty_fun b in
        (match uu____1458 with | (args,res) -> ((a :: args), res))
    | uu____1479 -> ([], t)
exception CallNotImplemented
let uu___is_CallNotImplemented: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | CallNotImplemented  -> true | uu____1486 -> false
let not_implemented_warning: Prims.string -> Prims.unit =
  fun t  ->
    FStar_Util.print1_warning ". Tactic %s will not run natively.\n" t
type emb_decl =
  | Embed
  | Unembed[@@deriving show]
let uu___is_Embed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Embed  -> true | uu____1495 -> false
let uu___is_Unembed: emb_decl -> Prims.bool =
  fun projectee  ->
    match projectee with | Unembed  -> true | uu____1500 -> false
let lid_to_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun l  ->
    let uu____1505 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
    FStar_Extraction_ML_Syntax.MLE_Name uu____1505
let lid_to_top_name: FStar_Ident.lident -> FStar_Extraction_ML_Syntax.mlexpr
  =
  fun l  ->
    let uu____1510 =
      let uu____1511 = FStar_Extraction_ML_Syntax.mlpath_of_lident l in
      FStar_Extraction_ML_Syntax.MLE_Name uu____1511 in
    FStar_All.pipe_left
      (FStar_Extraction_ML_Syntax.with_ty FStar_Extraction_ML_Syntax.MLTY_Top)
      uu____1510
let str_to_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  ->
    let uu____1516 = FStar_Ident.lid_of_str s in lid_to_name uu____1516
let str_to_top_name: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr =
  fun s  ->
    let uu____1521 = FStar_Ident.lid_of_str s in lid_to_top_name uu____1521
let fstar_syn_syn_prefix: Prims.string -> FStar_Extraction_ML_Syntax.mlexpr'
  = fun s  -> str_to_name (Prims.strcat "FStar_Syntax_Syntax." s)
let fstar_tc_common_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_TypeChecker_Common." s)
let fstar_refl_basic_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Basic." s)
let fstar_refl_data_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Reflection_Data." s)
let fstar_emb_basic_prefix:
  Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun s  -> str_to_name (Prims.strcat "FStar_Syntax_Embeddings." s)
let mk_basic_embedding:
  emb_decl -> Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun m  ->
    fun s  ->
      match m with
      | Embed  -> fstar_emb_basic_prefix (Prims.strcat "embed_" s)
      | Unembed  -> fstar_emb_basic_prefix (Prims.strcat "unembed_" s)
let mk_embedding:
  emb_decl -> Prims.string -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun m  ->
    fun s  ->
      match m with
      | Embed  -> fstar_refl_basic_prefix (Prims.strcat "embed_" s)
      | Unembed  -> fstar_refl_basic_prefix (Prims.strcat "unembed_" s)
let mk_tactic_unembedding:
  FStar_Extraction_ML_Syntax.mlexpr' Prims.list ->
    FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun args  ->
    let tac_arg = "t" in
    let reify_tactic =
      let uu____1568 =
        let uu____1569 =
          let uu____1576 =
            str_to_top_name "FStar_Tactics_Interpreter.reify_tactic" in
          let uu____1577 =
            let uu____1580 = str_to_top_name tac_arg in [uu____1580] in
          (uu____1576, uu____1577) in
        FStar_Extraction_ML_Syntax.MLE_App uu____1569 in
      FStar_All.pipe_left
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1568 in
    let from_tac =
      let uu____1584 =
        let uu____1585 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Builtins.from_tac_" uu____1585 in
      str_to_top_name uu____1584 in
    let unembed_tactic =
      let uu____1587 =
        let uu____1588 =
          FStar_Util.string_of_int
            ((FStar_List.length args) - (Prims.parse_int "1")) in
        Prims.strcat "FStar_Tactics_Interpreter.unembed_tactic_" uu____1588 in
      str_to_top_name uu____1587 in
    let app =
      match FStar_List.length args with
      | _0_45 when _0_45 = (Prims.parse_int "1") ->
          let uu____1590 =
            let uu____1597 =
              let uu____1600 =
                let uu____1601 =
                  let uu____1602 =
                    let uu____1609 =
                      let uu____1612 =
                        FStar_List.map
                          (FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top) args in
                      FStar_List.append uu____1612 [reify_tactic] in
                    (unembed_tactic, uu____1609) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1602 in
                FStar_Extraction_ML_Syntax.with_ty
                  FStar_Extraction_ML_Syntax.MLTY_Top uu____1601 in
              [uu____1600] in
            (from_tac, uu____1597) in
          FStar_Extraction_ML_Syntax.MLE_App uu____1590
      | n1 ->
          ((let uu____1621 = FStar_Util.string_of_int n1 in
            FStar_Util.print1_warning
              "Unembedding not defined for tactics of %s arguments\n"
              uu____1621);
           FStar_Exn.raise CallNotImplemented) in
    FStar_Extraction_ML_Syntax.MLE_Fun
      ([(tac_arg, FStar_Extraction_ML_Syntax.MLTY_Top);
       ("()", FStar_Extraction_ML_Syntax.MLTY_Top)],
        (FStar_Extraction_ML_Syntax.with_ty
           FStar_Extraction_ML_Syntax.MLTY_Top app))
let rec mk_tac_param_type:
  FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr' =
  fun t  ->
    let uu____1650 =
      let uu____1651 = FStar_Syntax_Subst.compress t in
      uu____1651.FStar_Syntax_Syntax.n in
    match uu____1650 with
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
        fstar_syn_syn_prefix "t_int"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
        fstar_syn_syn_prefix "t_bool"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
        fstar_syn_syn_prefix "t_unit"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid ->
        fstar_syn_syn_prefix "t_string"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1659 = FStar_Reflection_Data.fstar_refl_types_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1659 ->
        fstar_refl_data_prefix "t_binder"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1661 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1661 ->
        fstar_refl_data_prefix "t_term"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1663 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1663 ->
        fstar_refl_data_prefix "t_fv"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1665 = FStar_Reflection_Data.fstar_refl_syntax_lid "binder" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1665 ->
        fstar_refl_data_prefix "t_binders"
    | FStar_Syntax_Syntax.Tm_fvar fv when
        let uu____1667 =
          FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
        FStar_Syntax_Syntax.fv_eq_lid fv uu____1667 ->
        fstar_refl_data_prefix "t_norm_step"
    | FStar_Syntax_Syntax.Tm_app (h,args) ->
        let uu____1690 =
          let uu____1691 = FStar_Syntax_Subst.compress h in
          uu____1691.FStar_Syntax_Syntax.n in
        (match uu____1690 with
         | FStar_Syntax_Syntax.Tm_uinst (h',uu____1695) ->
             let uu____1700 =
               let uu____1701 = FStar_Syntax_Subst.compress h' in
               uu____1701.FStar_Syntax_Syntax.n in
             (match uu____1700 with
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.list_lid
                  ->
                  let arg_term =
                    let uu____1708 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1708 in
                  let uu____1723 =
                    let uu____1730 =
                      let uu____1731 = fstar_tc_common_prefix "t_list_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1731 in
                    let uu____1732 =
                      let uu____1735 =
                        let uu____1738 = mk_tac_param_type arg_term in
                        [uu____1738] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1735 in
                    (uu____1730, uu____1732) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1723
              | FStar_Syntax_Syntax.Tm_fvar fv when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.option_lid
                  ->
                  let arg_term =
                    let uu____1745 = FStar_List.hd args in
                    FStar_Pervasives_Native.fst uu____1745 in
                  let uu____1760 =
                    let uu____1767 =
                      let uu____1768 = fstar_tc_common_prefix "t_option_of" in
                      FStar_Extraction_ML_Syntax.with_ty
                        FStar_Extraction_ML_Syntax.MLTY_Top uu____1768 in
                    let uu____1769 =
                      let uu____1772 =
                        let uu____1775 = mk_tac_param_type arg_term in
                        [uu____1775] in
                      FStar_List.map
                        (FStar_Extraction_ML_Syntax.with_ty
                           FStar_Extraction_ML_Syntax.MLTY_Top) uu____1772 in
                    (uu____1767, uu____1769) in
                  FStar_Extraction_ML_Syntax.MLE_App uu____1760
              | uu____1778 ->
                  ((let uu____1780 =
                      let uu____1781 =
                        let uu____1782 = FStar_Syntax_Subst.compress h' in
                        FStar_Syntax_Print.term_to_string uu____1782 in
                      Prims.strcat
                        "Type term not defined for higher-order type "
                        uu____1781 in
                    FStar_Util.print_warning uu____1780);
                   FStar_Exn.raise CallNotImplemented))
         | uu____1783 ->
             (FStar_Util.print_warning "Impossible\n";
              FStar_Exn.raise CallNotImplemented))
    | uu____1785 ->
        ((let uu____1787 =
            let uu____1788 =
              let uu____1789 = FStar_Syntax_Subst.compress t in
              FStar_Syntax_Print.term_to_string uu____1789 in
            Prims.strcat "Type term not defined for " uu____1788 in
          FStar_Util.print_warning uu____1787);
         FStar_Exn.raise CallNotImplemented)
let rec mk_tac_embedding_path:
  emb_decl -> FStar_Syntax_Syntax.term -> FStar_Extraction_ML_Syntax.mlexpr'
  =
  fun m  ->
    fun t  ->
      let uu____1798 =
        let uu____1799 = FStar_Syntax_Subst.compress t in
        uu____1799.FStar_Syntax_Syntax.n in
      match uu____1798 with
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.int_lid ->
          mk_basic_embedding m "int"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bool_lid ->
          mk_basic_embedding m "bool"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.unit_lid ->
          mk_basic_embedding m "unit"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.string_lid ->
          mk_basic_embedding m "string"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1807 =
            FStar_Reflection_Data.fstar_refl_types_lid "binder" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1807 ->
          mk_embedding m "binder"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1809 = FStar_Reflection_Data.fstar_refl_types_lid "term" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1809 ->
          mk_embedding m "term"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1811 = FStar_Reflection_Data.fstar_refl_types_lid "fv" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1811 ->
          mk_embedding m "fvar"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1813 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "binders" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1813 ->
          mk_embedding m "binders"
      | FStar_Syntax_Syntax.Tm_fvar fv when
          let uu____1815 =
            FStar_Reflection_Data.fstar_refl_syntax_lid "norm_step" in
          FStar_Syntax_Syntax.fv_eq_lid fv uu____1815 ->
          mk_embedding m "norm_step"
      | FStar_Syntax_Syntax.Tm_app (h,args) ->
          let uu____1838 =
            let uu____1839 = FStar_Syntax_Subst.compress h in
            uu____1839.FStar_Syntax_Syntax.n in
          (match uu____1838 with
           | FStar_Syntax_Syntax.Tm_uinst (h',uu____1843) ->
               let uu____1848 =
                 let uu____1859 =
                   let uu____1860 = FStar_Syntax_Subst.compress h' in
                   uu____1860.FStar_Syntax_Syntax.n in
                 match uu____1859 with
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.list_lid
                     ->
                     let arg_term =
                       let uu____1877 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1877 in
                     let uu____1892 =
                       let uu____1895 = mk_tac_embedding_path m arg_term in
                       [uu____1895] in
                     let uu____1896 = mk_tac_param_type arg_term in
                     ("list", uu____1892, uu____1896, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.option_lid
                     ->
                     let arg_term =
                       let uu____1903 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1903 in
                     let uu____1918 =
                       let uu____1921 = mk_tac_embedding_path m arg_term in
                       [uu____1921] in
                     let uu____1922 = mk_tac_param_type arg_term in
                     ("option", uu____1918, uu____1922, false)
                 | FStar_Syntax_Syntax.Tm_fvar fv when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.tactic_lid
                     ->
                     let arg_term =
                       let uu____1929 = FStar_List.hd args in
                       FStar_Pervasives_Native.fst uu____1929 in
                     let uu____1944 =
                       let uu____1947 = mk_tac_embedding_path m arg_term in
                       [uu____1947] in
                     let uu____1948 = mk_tac_param_type arg_term in
                     ("list", uu____1944, uu____1948, true)
                 | uu____1951 ->
                     ((let uu____1953 =
                         let uu____1954 =
                           let uu____1955 = FStar_Syntax_Subst.compress h' in
                           FStar_Syntax_Print.term_to_string uu____1955 in
                         Prims.strcat
                           "Embedding not defined for higher-order type "
                           uu____1954 in
                       FStar_Util.print_warning uu____1953);
                      FStar_Exn.raise CallNotImplemented) in
               (match uu____1848 with
                | (ht,hargs,type_arg,is_tactic) ->
                    let hargs1 =
                      match m with
                      | Embed  -> FStar_List.append hargs [type_arg]
                      | Unembed  -> hargs in
                    if is_tactic
                    then
                      (match m with
                       | Embed  ->
                           (FStar_Util.print_warning
                              "Embedding not defined for tactic type\n";
                            FStar_Exn.raise CallNotImplemented)
                       | Unembed  -> mk_tactic_unembedding hargs1)
                    else
                      (let uu____1981 =
                         let uu____1988 =
                           let uu____1989 = mk_basic_embedding m ht in
                           FStar_Extraction_ML_Syntax.with_ty
                             FStar_Extraction_ML_Syntax.MLTY_Top uu____1989 in
                         let uu____1990 =
                           FStar_List.map
                             (FStar_Extraction_ML_Syntax.with_ty
                                FStar_Extraction_ML_Syntax.MLTY_Top) hargs1 in
                         (uu____1988, uu____1990) in
                       FStar_Extraction_ML_Syntax.MLE_App uu____1981))
           | uu____1995 ->
               (FStar_Util.print_warning "Impossible\n";
                FStar_Exn.raise CallNotImplemented))
      | uu____1997 ->
          ((let uu____1999 =
              let uu____2000 =
                let uu____2001 = FStar_Syntax_Subst.compress t in
                FStar_Syntax_Print.term_to_string uu____2001 in
              Prims.strcat "Embedding not defined for type " uu____2000 in
            FStar_Util.print_warning uu____1999);
           FStar_Exn.raise CallNotImplemented)
let mk_interpretation_fun:
  'Auu____2012 .
    FStar_Ident.lident ->
      FStar_Extraction_ML_Syntax.mlexpr' ->
        FStar_Syntax_Syntax.term ->
          (FStar_Syntax_Syntax.bv,'Auu____2012)
            FStar_Pervasives_Native.tuple2 Prims.list ->
            FStar_Extraction_ML_Syntax.mlexpr' FStar_Pervasives_Native.option
  =
  fun tac_lid  ->
    fun assm_lid  ->
      fun t  ->
        fun bs  ->
          try
            let arg_types =
              FStar_List.map
                (fun x  ->
                   (FStar_Pervasives_Native.fst x).FStar_Syntax_Syntax.sort)
                bs in
            let arity = FStar_List.length bs in
            let h =
              let uu____2080 =
                let uu____2081 = FStar_Util.string_of_int arity in
                Prims.strcat
                  "FStar_Tactics_Interpreter.mk_tactic_interpretation_"
                  uu____2081 in
              str_to_top_name uu____2080 in
            let tac_fun =
              let uu____2089 =
                let uu____2096 =
                  let uu____2097 =
                    let uu____2098 = FStar_Util.string_of_int arity in
                    Prims.strcat "FStar_Tactics_Native.from_tactic_"
                      uu____2098 in
                  str_to_top_name uu____2097 in
                let uu____2105 =
                  let uu____2108 = lid_to_top_name tac_lid in [uu____2108] in
                (uu____2096, uu____2105) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2089 in
            let tac_lid_app =
              let uu____2112 =
                let uu____2119 = str_to_top_name "FStar_Ident.lid_of_str" in
                (uu____2119,
                  [FStar_Extraction_ML_Syntax.with_ty
                     FStar_Extraction_ML_Syntax.MLTY_Top assm_lid]) in
              FStar_Extraction_ML_Syntax.MLE_App uu____2112 in
            let psc = str_to_name "psc" in
            let args =
              let uu____2126 =
                let uu____2129 =
                  FStar_List.map (mk_tac_embedding_path Unembed) arg_types in
                let uu____2132 =
                  let uu____2135 = mk_tac_embedding_path Embed t in
                  let uu____2136 =
                    let uu____2139 = mk_tac_param_type t in
                    let uu____2140 =
                      let uu____2143 =
                        let uu____2146 =
                          let uu____2149 = str_to_name "args" in [uu____2149] in
                        psc :: uu____2146 in
                      tac_lid_app :: uu____2143 in
                    uu____2139 :: uu____2140 in
                  uu____2135 :: uu____2136 in
                FStar_List.append uu____2129 uu____2132 in
              FStar_List.append [tac_fun] uu____2126 in
            let app =
              let uu____2151 =
                let uu____2152 =
                  let uu____2159 =
                    FStar_List.map
                      (FStar_Extraction_ML_Syntax.with_ty
                         FStar_Extraction_ML_Syntax.MLTY_Top) args in
                  (h, uu____2159) in
                FStar_Extraction_ML_Syntax.MLE_App uu____2152 in
              FStar_All.pipe_left
                (FStar_Extraction_ML_Syntax.with_ty
                   FStar_Extraction_ML_Syntax.MLTY_Top) uu____2151 in
            FStar_Pervasives_Native.Some
              (FStar_Extraction_ML_Syntax.MLE_Fun
                 ([("psc", FStar_Extraction_ML_Syntax.MLTY_Top);
                  ("args", FStar_Extraction_ML_Syntax.MLTY_Top)], app))
          with
          | CallNotImplemented  ->
              ((let uu____2188 = FStar_Ident.string_of_lid tac_lid in
                not_implemented_warning uu____2188);
               FStar_Pervasives_Native.None)