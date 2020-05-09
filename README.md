---
author: Ollie Charles
date-accepted: ""
ticket-url: ""
implemented: ""
---


# Table of Contents

1.  [Overloaded Constructors](#org4bedf50)
    1.  [Motivation](#orgfce3b6b)
    2.  [Proposed Change Specification](#org156a85c)
        1.  [The `IsRecord` Type Class](#orgc99295f)
        2.  [The `RecordField` Type Class](#org7b4cbc5)
        3.  [Solving `IsRecord` and `RecordField`](#orgfd5ac8c)
        4.  [Expression Desugaring](#org7ffaf4d)
        5.  [Pattern Match Desugaring](#org894f4c5)
    3.  [Examples](#orgb2cd820)
        1.  [Plain Data Types](#org3551663)
        2.  [`Wrapped`](#org198398e)
        3.  [`rel8`](#orge34b917)
    4.  [Effect and Interactions](#orgd597c26)
    5.  [Costs and Drawbacks](#org21542f0)
        1.  [Overloading Can Decrease Clarity](#orgb16c52d)
        2.  [Pattern Matches Become Total](#org422a34d)
    6.  [Alternatives](#orga05a676)
        1.  [`named`](#org12a99d6)
        2.  [Prisms](#org34b5cc6)
        3.  [PatternSynonyms](#orgec2cb62)
    7.  [Unresolved Questions](#org04ef63d)
    8.  [Implementation Plan](#orge7cd614)

This proposal is [discussed at this pull request](https://github.com/ghc-proposals/ghc-proposals/pull/0>). **After creating the pull request, edit this file again, update the number in the link, and delete this bold sentence.**


<a id="org4bedf50"></a>

# Overloaded Constructors

This is a proposal to overload the syntax of record construction and record pattern matching, such that users can overload the meaning of a constructor using Haskell&rsquo;s type class mechanism.


<a id="orgfce3b6b"></a>

## Motivation

Interactions with data types defined by GHC Haskell (from here referred to as just *Haskell*) are becoming increasingly overloaded. The recently accepted [record dot syntax](https://github.com/ghc-proposals/ghc-proposals/blob/master/proposals/0282-record-dot-syntax.rst) proposal extends the syntax of GHC to allow &ldquo;dot access&rdquo; into the fields of records, and does so via the `HasField` type class. This type class is wired into the compiler, but it also permits extra instances to be defined by users. These extra instances allow users to define fields on records that have no concrete representation, while allowing interaction with them naturally as if they were fields. For example, given

    data MyRecord = MyRecord { x :: Bool }
    
    newtype MyWrapper = MyWrapper MyRecord

we can define a **virtual** field `x` as:

    instance HasField "x" MyWrapper Bool where
      hasField (MyWrapper myRecord) = (setter, getter)
        where setter x' = MyWrapper myRecord { x = x' }
              getter = myRecord.x

The `MyWrapper` data type does not have a field `x :: MyWrapper -> Bool`, as one would get with record syntax, but due to the `HasField` instance we can present as interface as if it does:

    myWrapperBool :: MyWrapper -> Bool
    myWrapperBool myWrapper = myWrapper.x

However, while we&rsquo;ve overloaded field access, the illusion is shattered when we either construct or destruct `MyWrapper` using record constructor syntax or record pattern matching, respectively:

    -- Rejected, 'MyWrapper' does not have a field called x.
    myWrapperX :: MyWrapper -> Bool
    myWrapperX MyWrapper{ x } = x
    
    -- Rejected, for the same reason
    myWrapper :: MyWrapper
    myWrapper = MyWrapper { x = True }

In this proposal, we propose the syntax of `MyWrapper { x = x', y = y', etc }` (referred to as *record constructor syntax*) to be overloadable, both in expressions and pattern matching, allowing the above code to now be valid.


<a id="org156a85c"></a>

## Proposed Change Specification

In summary, the proposed changes are:

1.  `IsRecord` - a new type class.
2.  `RecordField` - a new type class.
3.  Special constraint solving for `IsRecord` and `RecordField`.
4.  New term rewriting rules for `RecordCon` `HsExpr` terms.
5.  New term rewriting rules for `RecConIn` `Pat` terms.

We will next look at these points in more detail.


<a id="orgc99295f"></a>

### The `IsRecord` Type Class

    {-# language DataKinds, KindSignatures, RankNTypes, TypeFamilies #-}
    
    class IsRecord (constructorName :: Symbol) (record :: Type) where
      data Field name record :: Type -> Type
      constructRecord :: (forall x. Field constructorName record x -> x) -> record
      destructRecord :: t -> Field constructorName record x -> x

`IsRecord` takes two arguments - the name of the constructor `constructorName` (specified as a type level `Symbol`), and the type of value being constructed `record`. `IsRecord` also specifies an associated type - `Field` - that encodes the name and type of fields in the record. Finally, `IsRecord` uses all of this information to allow for records to be constructed with `constructRecord`, and subsequently destructed using `destructRecord`.

The API here can be viewed through the more general concept of a representable functor, for those who like to consider things more abstractly. One can think of a record as being representable by a function mapping the names of fields to their underlying values.


<a id="org7b4cbc5"></a>

### The `RecordField` Type Class

The use of both `constructRecord` and `destructRecord` methods requires being able to provide values of the associated `Field` associated type. As this proposal suggests desugaring existing syntax into new expressions in the renamer, inhabitants of this type are unknown . In order to provide a bridge for desugaring, an auxiliary type class is used to help with name resolution:

    class RecordField (fieldName :: Symbol) constructor t a | constructor t fieldName -> a where
      provide :: a -> (forall field x. Field constructor t field x -> x) -> Field constructor t field x -> x
    
      field :: Field constructor t fieldName a

`provide` is used to populate a single field for `constructRecord`, and `field` is used to map type level `fieldName` symbols to their corresponding inhabitant in `Field`.

The type of `provide` may look somewhat elaborate, but considering a prototypical use of this method may help understand their meanings. In the call `provide x k`, we are constructing a function that has an apporpriate type to give to `constructRecord`. If `constructRecord` calls the function given by `provide x k` with compatible `Field`, `provide` will learn that `x ~ a`, and simply return `x`. If the `Field` is incompatible, the continuation `k` will be invoked with the unknown `Field`. This allows multiple `provide=s to be combined together to with function composition, to construct larger functions for =constructRecord`. Ultimately, chaining `provide` is an encoding of a `case` statement on `Field`, as:

    \k ->                            -- case field of
      provide @"f1" x $              --   F1 -> x
      provide @"f2" y $              --   F2 -> y
      provide @"f3" z $              --   F3 -> z
      k                              --   _  -> k (missing field catch all)

The story for `destructRecord` and `field` is more straight forward - we apply use `field @"f1"` to construct a `Field constructorName t "f1" a`, which we can then pass to `destructRecord` to view the contents of a particular field.

We can see the interaction between all methods in `IsRecord` and `RecordField` by the following:

    destructRecord (constructRecord @"T" @"MkT" (provide @"x" x ..)) (field @"x") = x


<a id="orgfd5ac8c"></a>

### Solving `IsRecord` and `RecordField`

This section of the proposal only proposes observable behavior, as the author is not familiar with the details of GHCs constraint solver with respect to classes like `Coercible` and `HasField`, that have special treatment.

Both `IsRecord` and `RecordField` are used in pattern matching and record construction, as we explain shortly, but in order to allow existing code to compile with this extension on, we need to be able to newly introduced `IsRecord` and `RecordField` constraints. With this extension turned on, whenever GHC needs to solve a `RecordField` constraint for a record constructor that is in scope (that is, the constructor is either defined in the current module or has been imported from another), it is as if the following type class were defined:

then when solving \`IsRecord\` constraints, it as if the following instance was defined:

    -- Assuming
    --
    --   T1( MkT1, t1f1 :: A1 -> T1, t1f2 :: A2 -> T1, ..., t1fn :: An )
    --
    -- is in scope
    
    instance IsRecord "MkT1" T1 where
      data Field "MkT1" T1 fieldName a where
        T1F1 :: Field "MkT1" T1 "t1f1" A1
        T1F2 :: Field "MkT1" T1 "t1f2" A2
        ...
        T1Fn :: Field "MkT1" T1 "t1fn" An
    
      construct f =
        MkT1 (f T1F1) (f T1F2) ... (f T1Fn)
    
      destruct a i =
        case i of
          T1F1 -> a.t1f1
          T1F2 -> a.t1f2
          ...
          T1F3 -> a.t1f3

For `RecordField` constraints, GHC will also solve these constraints as if the following instances were defined:

    instance RecordField "t1f1" "MkT1" T1 A1 where
      provide x k i = case i of { T1F1 -> x ; _ -> k i }
      field = T1F1
    
    instance RecordField "t1f2" "MkT1" T1 A2 where
      provide x k i = case i of { T1F2 -> x ; _ -> k i }
      field = T1F2
    
    ...
    
    instance RecordField "t1fn" "MkT1" T1 An where
      provide x k i = case i of { T1Fn -> x ; _ -> k i }
      field = T1Fn


<a id="org7ffaf4d"></a>

### Expression Desugaring

We desugar record constructor expressions (`RecordCon` terms in the `HsExpr` type) after renaming, replacing them with saturated `constructRecord` calls. Specifically,

-   GHC source is parsed as normal, producing \`RecordCon\` nodes.

-   The GHC renamer phase is applied, which enhances `RecordCon` nodes by resolving `NamedFieldPuns` and `RecordWildCards`. At this point, we have fully satured `RecordCon` nodes, where all fields have an associated expression.

-   The `RecordCon` node is entirely replaced with a new expresion, where the rewriting rules are explained in pseudo-Haskell as
    
        -- Rewrite the 'RecordCon' node itself to `construct`, applied to a type level
        -- string matching the unqualified constructor name, and repeated applications
        -- of 'provide'.
        rewrite (RecordCon constructorName fields) =
          [| construct
               @$(constructorName)
               ($(expandFields fields) $(missingFields))
          | ] |
        
        -- Each field is replaced with `provide`, applied to a type level string of the
        -- unqualified field name, and the
        expandFields (f : fs) = [| provide @$(fieldName f) @(fieldExpr f) |]
        expandFields [] = [| \k -> error "No value supplied for field" |]

We will see more detailed examples of this desugaring next, but it may be helpful to see the changes produced by this desugaring on a small example:

    before :: MyRecord
    before = MyRecord { x = e1, y = e2 }
    
    after :: MyRecord
    after = construct @"MyRecord" (provide @"x" e1 $ provide @"y" e2 $ error "No value supplied for field")


<a id="org894f4c5"></a>

### Pattern Match Desugaring

A similar treatment is given to pattern matching, but rather than desugaring to a single application of `construct`, we desugar to repeated applications of `destruct`.

-   GHC source is parsed as normal, producing `ConPatIn` nodes, with `RecCon` values.

-   The GHC renamer phase is applied, which the `HsRecFields` value inside the `RecCon` of a `ConPatIn` node with the desugaring of named field puns and record wild cards.

-   This proposal adds an extra step, replacing `ConPatIn RecCon` patterns with a view patter instead. This rewriting can be explained via the following pseudo Haskell:
    
        rewrite (ConPatIn con (RecCon HsRecFields{rec_flds})) =
          [| ( \x -> $( destructRecFlds con rec_flds ) ) -> $( detuple rec_flds ) ]
        
        destructRecFlds [] = ()
        destructRecFlds (f : fs) =
          [| ( destruct @$( con ) x ( field @$( con ) @$( hsRecFieldLbl f ) )
             , destructRecFlds fs
             ) $]
        
        detuple [] = $( () )
        detuple (x:xs) = [| ( $( recFieldArg x ), $( detuple xs ) ) |]

Essentially, this desugaring is replace the record constructor pattern matching with a view pattern that first constructs a tuple of **n** applications of `destruct`, and then uses a view pattern to further pattern match on the result:

    before :: MyRecord -> A
    before MyRecord{x = x'} = x'
    
    after :: MyRecord -> A
    after ((\x -> (destruct @"MyRecord" (field @"MyRecord" @"x"), ())) -> (x', ())) = x'


<a id="orgb2cd820"></a>

## Examples


<a id="org3551663"></a>

### Plain Data Types

As a first example, we consider the behavior of the extension with ordinary Haskell data types. In this example GHC ultimately produces the semantically identical code to compilation without the extension, but we will still show the desugaring for clarity.

To start, take

    data Status = Passed | Failed | Incomplete | Withdrawn
    
    data Taken =
      Taken { year :: Int
            , term :: Quarter
            }
    
    data Class =
      Class { result :: Status
            , taken :: Taken
            }

as defined in TODO

We can construct and destruct these records as:

    haskellClass :: Class
    haskellClass =
      Class { result = Passed, taken = Taken { year = 2020, term = Winter } }
    
    classQuarter :: Quarter
    classQuarter Class{ taken = Taken{ term } } = term

The desugaring is:

    haskellClass :: Class
    haskellClass =
      construct @"Class" $
      provide @"result" Passed $
      provide @"taken" (construct @"Taken" $ provide @"year" 2020 $ provide @"term" Winter)
    
    classQuarter :: Quarter
    classQuarter
      ((\x -> (destruct @"Class" x (field @"Class" @"taken"), ())) -> (((\x -> (destruct @"Class" x (field @"Class" @"term"), ())) -> (term, ())))) = term

Using the following automatically generated instances.

    instance IsRecord "Class" Class where
      data Field "Class" Class fieldName a where
        ClassResult :: Field"Class" Class "result" Status
        ClassTaken :: Field "Class" Class "taken" Taken
    
      construct f =
        Class (f ClassResult) (f ClassTaken)
    
      destruct Class{..} = \class
        ClassResult -> result
        ClassTaken -> taken
    
    instance IsRecord "Taken" Taken where
      data Field "Taken" Taken fieldName a where
        TakenYear :: Field "Taken" Taken "year" Int
        TakenQuarter :: Field "Taken" Taken "quarter" Quarter
    
      construct f =
        Taken (f TakenYear) (f TakenQuarter)
    
      destruct Taken{..} = \case
        TakenYear -> year
        TakenQuarter -> quarter


<a id="org198398e"></a>

### `Wrapped`

As a first example,

This section illustrates the specification through the use of examples of the language change proposed. It is best to exemplify each point made in the specification, though perhaps one example can cover several points. Contrived examples are OK here. If the Motivation section describes something that is hard to do without this proposal, this is a good place to show how easy that thing is to do with the proposal.


<a id="orge34b917"></a>

### TODO `rel8`


<a id="orgd597c26"></a>

## TODO Effect and Interactions

The primary effect of this proposal is to allow data types to have virtual constructors that have no concrete representation. This opens up a design space previously inaccessible to users of Haskell.

This proposal interacts with other extensions that extend record constructor syntax - namely `NamedFieldPuns` and `RecordWildCards`. This interaction is by design, it is precisely this interaction that we want to allow, as these extensions appear frequently in user code.

Discuss possibly contentious interactions with existing language or compiler features.


<a id="org21542f0"></a>

## Costs and Drawbacks

Give an estimate on development and maintenance costs. List how this effects learnability of the language for novice users. Define and list any remaining drawbacks that cannot be resolved.


<a id="orgb16c52d"></a>

### TODO Overloading Can Decrease Clarity

Every time something becomes more polymorphic there is a risk that code becomes less clear.


<a id="org422a34d"></a>

### Pattern Matches Become Total

The largest drawback of this proposal is that record pattern matching is now required to be total. We can understand this by considering type of the primitive `destructRecord` operation:

    destructRecord :: IsRecord constructor t => t -> Field constructor t x -> x

That is, given a value of type `t` and a `Field` compatible with `t`, `destructRecord` is *guaranteed* to return a value. In general, this does not match the behavior of Haskell, as the following code has different meanings depending on whether or not the extension is present:

    data Two = One { x :: Bool } | Two { y :: Bool }
    
    f :: Two -> Bool
    f One { x } = x
    f Two { y } = y

Without the extension enabled `f (Two True)` will return `True`, but with the extension enabled the same expression will crash, as `Two True` doesn&rsquo;t have the field `x`, as required by the pattern match one `One`.

The immediate reaction might be to change `destructRecord` to be explicitly partial, perhaps by returning a `Maybe`. However, this just moves the problem - now pattern matching is always inexhaustive, even if a type only has one constructor! The problem appears fairly fundamental to the open nature of type classes. This proposal has decided to make record pattern matching exhaustive as in the majority of cases records with multiple constructors are generally considered by the community to be a bad idea.

The [`total`](https://hackage.haskell.org/package/total) library demonstrates how one can have total pattern matching using prisms, but this is only applicable to a subset of types. Namely, the library mentions the following caveat:

> You can also implement exhaustive pattern matching for your own data types with Traversals or Prisms. However, this only works if you have one type variable for each branch of your type


<a id="orga05a676"></a>

## Alternatives


<a id="org12a99d6"></a>

### `named`

The current alternative that is used in practice is to invent new constructor syntax directly in Haskell. The `named` library, as used by `higgledy` is one such approach. This library offers a new &ldquo;syntax&rdquo; (a combination of infix operators and type level programming) for constructing functions of named arguments, which in a sense can be viewed as constructing a record of fields.

The `higgledy` library uses `named` with it&rsquo;s [Record](http://hackage.haskell.org/package/higgledy-0.3.1.0/docs/Data-Generic-HKD-Named.html) class, allowing users to construct data with named arguments. The documentation provides this example:

    data User
      = User { name :: String, age :: Int, likesDogs :: Bool }
      deriving Generic``haskell
    
    test :: _
    test = record @User

    ...
    ... Found type wildcard ...
    ... standing for ...("name" :! f [Char])
    ...   -> ("enemy" :! f [Char]) -> HKD User f...
    ...

This function can be called using repeated application of `named`&rsquo;s `!` operator and overloaded fields.

    user :: HKD Maybe User
    user =
      test ! #name (Just "ocharles")
           ! #age (Just 30)
           ! #likesDog Nothing

This approach has numerous drawbacks compared to the proposal:

-   Use of the `test` function has required users to learn the interface of the `named` library, which introduces a new and non-standard way to construct records.

-   A new syntactic idiom means this approach will likely struggle with automatic code formatters (though this is solvable, if formatters implement name resolution and special-case this syntax).

-   Use of this function requires the `OverloadedLabels` extension, which introduces new syntax.

-   This approach is not symmetric - there is no way for users to use this syntax in pattern matching.

-   This function is incompatible with `NamedFieldPuns` and `RecordWildCards`. For example, one might like to write:
    
        data DetailedUser = DetailedUser
          { name :: String
          , age :: String
          , likesDogs :: Bool
          , likesCoffee :: Bool
          }
        
        liftUser :: HKD Maybe User -> HKD Maybe User
        liftUser HKD{ name, age } = -- 1
          DetailedUser
            ! #name                 -- 2
            ! #age                  -- 2
            ! #likesDogs Nothing
            ! #likesCoffee Nothing
    
    But this is not possible for two reasons:
    
    1.  This pattern match is not possible, and is the motivation of this very proposal.
    
    2.  The use of the `!` operator needs a name and value, but here we are only supplying a name and inferring the value from the ambient environment at the callsite. But library code has no access to this environment.
    
    Instead we are forced to write:
    
        data DetailedUser = DetailedUser
          -- as before
        
        liftUser :: HKD Maybe User -> HKD Maybe User
        liftUser user =
          let userName = user.name
              userAge = user.age
          in
          DetailedUser
            ! #name userName
            ! #age userAge
            ! #likesDogs Nothing
            ! #likesCoffee Nothing
    
    which simulatenously increases verbosity and obscures the meaning of this function.


<a id="org34b5cc6"></a>

### Prisms

The prolific work on lenses over the years has discovered a new abstraction - prisms. While lenses provide a way to focus in on a component of a product type, prisms are the &ldquo;dual&rdquo; to this, providing the ability to focus on an alternative of a sum type. They provide both the ability to construct values (totally) and destruct values (partially).

Without defining what a `Prism` is, the `optics` library provides:

    type Prism s t a b
    
    preview :: Prism s s a a -> s -> Maybe a
    review :: Prism s s a a -> a -> s

`preview` is analogous to pattern matching on a particular constructor, and `review` is analogous to constructing a value using a particular constructor.

Prisms are not without their drawbacks in this area though:

-   Prisms generally require uncurrying the constructor through a tuple. This is not a huge drawback, as when one uses record constructors they are similarily forced to supply a product. The real problem here is the tuple loses the named aspect of records - a prism that views a constructor as a tuple of values and forgets the names (and enforces an ordering) is less ergonomic than records.

-   Like `named`, prisms are a new concept users have to learn on top of Haskell&rsquo;s traditional record syntax.

-   Prisms are also incompatible with `NamedFieldPuns` and `RecordWildCards`. It would be nice to be able to construct values with prisms by using values implicitly inscope (ala `NamedFieldPuns`), but this is not currently possible.

-   As prisms are values, their names have to exist Haskells variable namespace, which prohibits names that match constructors. In practice, this has lead to a naming convention of using a leading `_`, such as `_Just` and `_Nothing`. However, along with looking slighty unsatisfactory, this naming convention interacts poorly with GHC, as a leading underscore stops GHC from checking for unused declarations and imports.

-   Interaction with prisms require the use of combinators like `preview` and `review`. While this is a small cost, it is still a barrier to use. This cost can occasionally be avoided by defining a prism and then interacting with the prism with pattern synonyms.

Prisms offer a very promising alternative, but losing record syntax still feels like a cost that is too high when we&rsquo;re considering appyling the techinque is this proposal extensively. Were Haskell to have first-class anonymous records, prisms would likely be a much more viable approach. One could imagine being able to write prisms like:

    data MyRecord = MyRecord {x, y :: Bool }
    
    myRecordPrism :: Prism MyRecord {x, y :: Bool}
    
    myRecord :: MyRecord
    myRecord = review myRecordPrism { x = True, y = False }

but this is not currently possible.


<a id="orgec2cb62"></a>

### PatternSynonyms

Pattern synonyms are the closest existing feature to what is proposed here, but has one significant drawback - as pattern synonyms are not first class, they cannot be generated. This means that a data type must define all pattern synonyms statically, but for something like `Wrapped` that lifts all fields of *any* data type to be wrapped by another type, we don&rsquo;t know what constructors we would need to define.

For example, assume `Wrapped` is defined in a library (like `HKD` from `higgledy`). In this case, we don&rsquo;t know how a user will use `Wrapped`, so we are unable to supply an appropriate pattern synonym:

    module Library ( Wrapped ) where
    newtype Wrapped (f :: Type -> Type) (a :: Type) = ...
    
    
    module UserCode ( Wrapped ) where
    
    data Record = Record { x :: T }
    
    pattern WrappedRecord :: f T -> Wrapped f Record
    pattern WrappedRecord{ x } = ...omitted
    
    record :: Wrapped Maybe Record
    record = Record { x = Just True }

This is unsatisfactory as users now have to write an explicit pattern synonym out for every use of `Wrapped`, where we would prefer to derive this automatically.


<a id="org04ef63d"></a>

## TODO Unresolved Questions

Explicitly list any remaining issues that remain in the conceptual design and specification. Be upfront and trust that the community will help. Please do not list **implementation** issues.

Hopefully this section will be empty by the time the proposal is brought to the steering committee.


<a id="orge7cd614"></a>

## Implementation Plan

This work has been prototyped in the [`is-record` GHC plugin](https://github.com/ocharles/is-record-plugin). It is hoped that this work will be directly applicable to GHC itself, as it uses the GHC API, though it is expected further work will be required to finess the implementation.

