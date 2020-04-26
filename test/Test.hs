{-# language DataKinds #-}
{-# language FlexibleContexts #-}
{-# language GADTs #-}
{-# language MultiParamTypeClasses #-}
{-# language NamedFieldPuns #-}
{-# language RecordWildCards #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}

{-# options -ddump-simpl #-}
{-# options -fplugin=Plugin #-}

module Test where

data T =
  MyRecord { x, y, z :: Bool }
  deriving (Show)


-- myRecord :: Bool -> T
myRecord y =
  let z = True
  in MyRecord { x = True, y, .. }
