{-# language GADTs #-}
{-# language LambdaCase #-}
{-# language NamedFieldPuns #-}

module Plugin where

import Data.Generics.Uniplate.Data
import Control.Monad ( guard )
import Bag
import HsSyn
import HsExtension
import GhcPlugins
import TcEvidence
import RnEnv
import RnExpr
import HsDumpAst
import GHC

plugin :: Plugin
plugin =
  defaultPlugin
    { parsedResultAction = \_cliOptions _modSummary x ->
        pure x { hpm_module = onModule <$> hpm_module x }
    , renamedResultAction = \_cliOptions tcGblEnv x -> do
        (constructExpr, _) <- rnLExpr $ noLoc $ HsVar noExt $ noLoc $ mkRdrQual isRecordModule $ mkVarOcc "construct"
        (provideExpr, _) <- rnLExpr $ noLoc $ HsVar noExt $ noLoc $ mkRdrQual isRecordModule $ mkVarOcc "provide"
        (undefinedExpr, _) <- rnLExpr $ noLoc $ HsVar noExt $ noLoc $ mkRdrQual (mkModuleName "Prelude") $ mkVarOcc "undefined"

        pure ( tcGblEnv, descendBi (generaliseConstructorApplications constructExpr provideExpr undefinedExpr) x )
    , pluginRecompile =
        purePlugin
    }


onModule :: HsModule GhcPs -> HsModule GhcPs
onModule x =
  x { hsmodImports =
        onImports $ hsmodImports x
    , hsmodDecls =
           concatMap isRecordInstances (hsmodDecls x)
        ++ hsmodDecls x
    }


onImports :: [LImportDecl GhcPs] -> [LImportDecl GhcPs]
onImports =
  (isRecordImport :)


isRecordImport :: LImportDecl GhcPs
isRecordImport =
  qualifiedImplicitImport isRecordModule


isRecordModule =
  mkModuleName "IsRecord"


qualifiedImplicitImport :: ModuleName -> LImportDecl GhcPs
qualifiedImplicitImport x =
  noLoc $ ImportDecl noExt NoSourceText (noLoc x) Nothing False False True True Nothing Nothing


isRecordInstances :: LHsDecl GhcPs -> [LHsDecl GhcPs]
isRecordInstances (L l (TyClD _ (DataDecl _ tname vars _fixity defn))) = do
  guard (dd_ND defn == DataType)

  L _ conDecl <- dd_cons defn

  L _ name <-
    case conDecl of
      ConDeclGADT{ con_names } -> con_names
      ConDeclH98{ con_name } -> [ con_name ]

  fields <-
    case con_args conDecl of
      PrefixCon prefixArgs -> []
      RecCon (L _ fields) ->
        return fields

  let dataTy = noLoc (HsTyVar noExt NotPromoted tname)

  let constructorNameType = noLoc $ HsTyLit noExt $ HsStrTy NoSourceText $ occNameFS $ rdrNameOcc name

  let isRecordInstance =
        L l $ InstD noExt $ ClsInstD noExt $ ClsInstDecl
          { cid_ext = noExt
          , cid_poly_ty = HsIB noExt $
              mkHsAppTys
                (noLoc $ HsTyVar noExt NotPromoted (noLoc $ mkRdrQual isRecordModule $ mkClsOcc "IsRecord"))
                [ constructorNameType
                , dataTy
                ]
          , cid_binds = unitBag $ noLoc $ FunBind
              { fun_ext = noExt
              , fun_id = noLoc $ mkRdrUnqual $ mkVarOcc "construct"
              , fun_matches = MG
                  { mg_ext = noExt
                  , mg_alts = noLoc $ pure $ noLoc $ Match
                      { m_ext = noExt
                      , m_ctxt = FunRhs
                          { mc_fun = noLoc $ mkRdrUnqual $ mkVarOcc "construct"
                          , mc_fixity = Prefix
                          , mc_strictness = NoSrcStrict
                          }
                      , m_pats =
                          [ noLoc $ VarPat noExt $ noLoc $ mkRdrUnqual $ mkVarOcc "f" ]
                      , m_grhss = GRHSs
                          { grhssExt = noExt
                          , grhssGRHSs =
                              pure $
                              noLoc $
                              GRHS noExt [] $
                              foldl
                                (\x y -> noLoc $ HsApp noExt x y)
                                (noLoc $ HsVar noExt $ noLoc name)
                                (do L _ conDeclField <- fields
                                    L _ fieldOcc <- cd_fld_names conDeclField

                                    let L _ conName = rdrNameFieldOcc fieldOcc
                                    let i = "F_" ++ occNameString (rdrNameOcc conName)

                                    return $ noLoc $ HsApp noExt
                                      (noLoc $ HsVar noExt $ noLoc $ mkRdrUnqual $ mkVarOcc "f")
                                      (noLoc $ HsVar noExt $ noLoc $ mkRdrUnqual $ mkDataOcc i)
                                )
                          , grhssLocalBinds = noLoc $ EmptyLocalBinds noExt
                          }
                      }
                  , mg_origin = Generated
                  }
              , fun_co_fn = WpHole
              , fun_tick = []
              }
          , cid_sigs = []
          , cid_tyfam_insts = []
          , cid_datafam_insts = pure $ noLoc $ DataFamInstDecl $ HsIB noExt $ FamEqn
              { feqn_ext = noExt
              , feqn_tycon = noLoc $ mkRdrUnqual $ mkTcOcc "Field"
              , feqn_pats =
                  [ constructorNameType
                  , dataTy
                  , noLoc $ HsTyVar noExt NotPromoted $ noLoc $ mkRdrUnqual $ mkTyVarOcc "fieldName"
                  , noLoc $ HsTyVar noExt NotPromoted $ noLoc $ mkRdrUnqual $ mkTyVarOcc "x"
                  ]
              , feqn_fixity = Prefix
              , feqn_rhs = HsDataDefn
                  { dd_ext = noExt
                  , dd_ND = DataType
                  , dd_ctxt = noLoc []
                  , dd_cType = Nothing
                  , dd_kindSig = Nothing
                  , dd_cons = do
                      L _ conDeclField <- fields
                      L _ fieldOcc <- cd_fld_names conDeclField

                      let L _ conName = rdrNameFieldOcc fieldOcc

                      pure $ noLoc $ ConDeclGADT
                        { con_g_ext = noExt
                        , con_names =
                            [ noLoc $ mkRdrUnqual $ mkDataOcc $
                              "F_" ++ occNameString (rdrNameOcc conName)
                            ]
                        , con_forall = noLoc False
                        , con_qvars = HsQTvs noExt []
                        , con_mb_cxt = Nothing
                        , con_args = PrefixCon []
                        , con_res_ty =
                            mkHsAppTys
                              (noLoc $ HsTyVar noExt NotPromoted $ noLoc $ mkRdrQual isRecordModule $ mkTcOcc "Field")
                              [ constructorNameType
                              , dataTy
                              , noLoc $ HsTyLit noExt $ HsStrTy NoSourceText $ occNameFS $ rdrNameOcc conName
                              , cd_fld_type conDeclField
                              ]
                        , con_doc = Nothing
                        }

                  , dd_derivs = noLoc []
                  }
              }
          , cid_overlap_mode = Nothing
          }

  let recordFieldInstance conDeclField fieldOcc =
        let
          L _ conName = rdrNameFieldOcc fieldOcc

          fieldNameTyLit = noLoc $ HsTyLit noExt $ HsStrTy NoSourceText $
            occNameFS $ rdrNameOcc conName

          iName = mkRdrUnqual $ mkDataOcc $ "F_" ++ occNameString (rdrNameOcc conName)

        in
        L l $ InstD noExt $ ClsInstD noExt $ ClsInstDecl
          { cid_ext = noExt
          , cid_poly_ty = HsIB noExt $
              mkHsAppTys
                (noLoc $ HsTyVar noExt NotPromoted (noLoc $ mkRdrQual isRecordModule $ mkClsOcc "RecordField"))
                [ fieldNameTyLit
                , constructorNameType
                , dataTy
                , cd_fld_type conDeclField
                ]
          , cid_binds = unitBag $ noLoc $ FunBind
              { fun_ext = noExt
              , fun_id = noLoc $ mkRdrUnqual $ mkVarOcc "provide"
              , fun_matches = MG
                  { mg_ext = noExt
                  , mg_alts = noLoc $ pure $ noLoc $ Match
                      { m_ext = noExt
                      , m_ctxt = FunRhs
                          { mc_fun = noLoc $ mkRdrUnqual $ mkVarOcc "provide"
                          , mc_fixity = Prefix
                          , mc_strictness = NoSrcStrict
                          }
                      , m_pats =
                          [ noLoc $ VarPat noExt $ noLoc $ mkRdrUnqual $ mkVarOcc "x"
                          , noLoc $ VarPat noExt $ noLoc $ mkRdrUnqual $ mkVarOcc "k"
                          , noLoc $ VarPat noExt $ noLoc $ mkRdrUnqual $ mkVarOcc "i"
                          ]
                      , m_grhss = GRHSs
                          { grhssExt = noExt
                          , grhssGRHSs =
                              pure $
                              noLoc $
                              GRHS noExt [] $
                              noLoc $ HsCase noExt (noLoc $ HsVar noExt $ noLoc $ mkRdrUnqual $ mkVarOcc "i") $
                              MG
                                { mg_ext = noExt
                                , mg_alts = noLoc
                                    [ noLoc $ Match
                                        { m_ext = noExt
                                        , m_ctxt = CaseAlt
                                        , m_pats = pure $ noLoc $ ConPatIn
                                            (noLoc iName)
                                            (PrefixCon [])
                                        , m_grhss = GRHSs
                                            { grhssExt = noExt
                                            , grhssGRHSs = pure $ noLoc $ GRHS noExt [] $ noLoc $ HsVar noExt $ noLoc $ mkRdrUnqual $ mkVarOcc "x"
                                            , grhssLocalBinds = noLoc $ EmptyLocalBinds noExt
                                            }
                                        }
                                    , noLoc $ Match
                                        { m_ext = noExt
                                        , m_ctxt = CaseAlt
                                        , m_pats = pure $ noLoc $ WildPat noExt
                                        , m_grhss = GRHSs
                                            { grhssExt = noExt
                                            , grhssGRHSs = pure $ noLoc $ GRHS noExt [] $ noLoc $
                                                HsApp noExt
                                                  (noLoc $ HsVar noExt $ noLoc $ mkRdrUnqual $ mkVarOcc "k")
                                                  (noLoc $ HsVar noExt $ noLoc $ mkRdrUnqual $ mkVarOcc "i")
                                            , grhssLocalBinds = noLoc $ EmptyLocalBinds noExt
                                            }
                                        }
                                    ]
                                , mg_origin = Generated
                                }

                          , grhssLocalBinds = noLoc $ EmptyLocalBinds noExt
                          }
                      }
                  , mg_origin = Generated
                  }
              , fun_co_fn = WpHole
              , fun_tick = []
              }
          , cid_sigs = []
          , cid_tyfam_insts = []
          , cid_datafam_insts = []
          , cid_overlap_mode = Nothing
          }


  let recordFieldInstances = do
        L _ conDeclField <- fields
        L _ fieldOcc <- cd_fld_names conDeclField
        return $ recordFieldInstance conDeclField fieldOcc

  isRecordInstance : recordFieldInstances

isRecordInstances _ =
  []


generaliseConstructorApplications :: LHsExpr GhcRn -> LHsExpr GhcRn -> LHsExpr GhcRn -> LHsExpr GhcRn -> LHsExpr GhcRn
generaliseConstructorApplications construct provide undefinedE = \case
  L l1 (RecordCon _ (L conLoc conName) fields) ->
    noLoc $ HsApp noExt
      (noLoc $ HsAppType
         (HsWC [] $ noLoc $ HsTyLit noExt $ HsStrTy NoSourceText $ occNameFS $ nameOccName $ conName)
         construct)
      (foldl
        (\y x -> noLoc $ HsApp noExt x y)
        undefinedE
        (map provideField (rec_flds fields)))
    where
      provideField (L _ HsRecField{ hsRecFieldLbl, hsRecFieldArg }) =
        noLoc $
          HsApp noExt
            (noLoc $
            HsAppType
              (HsWC [] $ noLoc $ HsTyLit noExt $ HsStrTy NoSourceText $ occNameFS $ rdrNameOcc $ unLoc $ rdrNameFieldOcc $ unLoc hsRecFieldLbl )
              provide)
            hsRecFieldArg

  x -> descend (generaliseConstructorApplications construct provide undefinedE) x
