{-# language AllowAmbiguousTypes #-}
{-# language BlockArguments #-}
{-# language DataKinds #-}
{-# language GADTs #-}
{-# language FlexibleInstances #-}
{-# language FunctionalDependencies #-}
{-# language KindSignatures #-}
{-# language LambdaCase #-}
{-# language RankNTypes #-}
{-# language TypeApplications #-}
{-# language TypeFamilies #-}

module IsRecord where

import GHC.TypeLits ( Symbol )
import Data.Kind ( Type )


class IsRecord (name :: Symbol) (t :: Type) where
  data Field name t :: Symbol -> Type -> Type
  construct :: (forall field x. Field name t field x -> x) -> t


class RecordField (fieldName :: Symbol) constructor t a | constructor t fieldName -> a where
  provide :: a -> (forall field x. Field constructor t field x -> x) -> Field constructor t field x -> x
