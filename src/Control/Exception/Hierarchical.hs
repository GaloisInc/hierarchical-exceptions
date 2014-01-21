{- Control.Exception.Hierarchical -- Template Haskell for defining exceptions
Copyright (C) 2014 Galois, Inc.

Licensed under the Apache License, Version 2.0 (the "License"); you may not use
this file except in compliance with the License.  You may obtain a copy of the
License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed
under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
CONDITIONS OF ANY KIND, either express or implied.  See the License for the
specific language governing permissions and limitations under the License. -}

{-| "Control.Exception" leverages "Data.Typeable" to fake subtyping and thereby
give Haskell support for hierarchies of exceptions.  However, defining
exception hierarchies requires quite a bit of boilerplate.  For instance, to
define

  * a top-level exception, 'TracerException',

  * a sub-exception, 'TimingFailure', and

  * a sub-exception, 'WriteFailure',

requires several paragraphs of code:

> import Control.Exception
> import Data.Typeable (Typeable, cast)
>
> data TracerException = forall e. Exception e => TracerException e
>                      deriving Typeable
>
> instance Show TracerException where
>   show (TracerException e) = show e
>
> instance Exception TracerException
>
> data TimingFailure = TimingFailure
>                    deriving (Show, Typeable)
>
> instance Exception TimingFailure where
>   toException = toException . TracerException
>   fromException x = do
>     TracerException a <- fromException x
>     cast a
>
> data WriteFailure = WriteFailure
>                   deriving (Show, Typeable)
>
> instance Exception WriteFailure where
>   toException = toException . TracerException
>   fromException x = do
>     TracerException a <- fromException x
>     cast a

Instead of writing this, one could simply write

> import Control.Exception (SomeException(SomeException))
> import Control.Exception.Hierarchical
>
> mkAbstractException 'SomeException "TracerException"
> mkException 'TracerException "TimingFailure"
> mkException 'TracerException "WriteFailure"

and allow Template Haskell to fill in the rest.

This libray deals with two types of exceptions: /abstract/ and /concrete/
exceptions.  Both types can be caught with 'Control.Exception.catch' and other
associated functions; however, only you may only extend abstract exceptions,
and you may only throw concrete ones.  This is a fundamental limitation of the
Haskell exception hierarchy system as it currently exists. -}

{-# LANGUAGE TemplateHaskell #-}

module Control.Exception.Hierarchical
       ( mkAbstractException
       , mkException
       ) where

import Control.Exception (Exception, SomeException(SomeException))
import Control.Monad ((<=<), liftM)
import Data.Typeable (Typeable, cast)
import Language.Haskell.TH


--------------------------- Hierarchies and casting ----------------------------

{-| Creates declarations to make a data type a sub-exception of another
exception.  This is best illustrated by some examples:

>   exceptionDeclaration 'SomeException 'MyAbstractException
> ======>
>   instance Exception MyAbstractException

>   exceptionDeclaration 'MyAbstractException 'MyConcreteException
> ======>
>   instance Exception MyConcreteException where
>     toException = toException . MyConcreteException
>     fromException = fromException >=> \(MyAbstractException x) -> cast x

Note that exceptions directly under 'SomeException' are special-cased; the
default implementation for the 'Exception' type class is sufficient in this
case. -}
exceptionDeclaration :: Name    -- ^ the name of the super-exception
                        -> Name -- ^ the name of the sub-exception
                        -> DecsQ
exceptionDeclaration super name =
  one $ instanceD' (cxt [])
                   [t| Exception $(conT name) |]
                   (if super == 'SomeException
                    then
                      {- 'name' is directly under 'SomeException', so use the
                      default implementation for the conversion functions. -}
                      return []
                    else
                      {- 'name' is directly under some other exception, so
                      explicitly define the conversion functions to set up the
                      hierarchy correctly. -}
                      exceptionHierarchyFunctions super)

{-| Creates declarations to implement the 'Exception' instance for a
sub-exception. -}
exceptionHierarchyFunctions :: Name -- ^ the name of the super-exception
                               -> DecsQ
exceptionHierarchyFunctions super =
  [d| toException   = toException . sup
        where sup = $(conE super)
      fromException = cast . sub <=< fromException
        where sub = $(destruct1 super) |]



----------------------------- Abstract exceptions ------------------------------

{-| Creates an /abstract/ sub-exception of an existing exception.  As discussed
in the introduction, such an exception cannot be thrown; it can only be
extended. -}
mkAbstractException :: Name
                       -- ^ the name of the super-exception’s data constructor
                       -> String -- ^ the name of the exception to create
                       -> DecsQ
mkAbstractException super name =
  let name' = mkName name in
  many [ abstractDataDeclaration name'
       , abstractShowDeclaration name'
       , exceptionDeclaration super name' ]

{-| Defines a new data type suitable for use as an abstract exception.  For
example,

>   abstractDataDeclaration (mkName "Name")
> ======>
>   data Name = forall e. Exception e => Name e
>             deriving Typeable -}
abstractDataDeclaration :: Name -> DecsQ
abstractDataDeclaration name =
  one $ dataD (cxt []) name []
              [let e = mkName "e" in
               forallC [PlainTV e]
                       (cxt [classP ''Exception [varT e]])
                       (normalC name [return (NotStrict, VarT e)])]
              [''Typeable]

{-| Creates an instance declaration for an abstract exception type.  For
example,

>   abstractShowDeclaration ''Name
> ======>
>   instance Show Name where
>     show (Name e) = show e -}
abstractShowDeclaration :: Name -> DecsQ
abstractShowDeclaration name =
  one $ instanceD' (cxt [])
                   [t| Show $(conT name) |]
                   [d| show = show . $(destruct1 name) |]


----------------------------- Concrete exceptions -----------------------------

{-| Creates a /concrete/ sub-exception of an existing exception.  As discussed
in the introduction, such an exception cannot be extended; it can only be
thrown. -}
mkException :: Name
               -- ^ the name of the super-exception’s data constructor
               -> String        -- ^ the name of the exception to create
               -> DecsQ
mkException super name =
  let name' = mkName name in
  many [ dataDeclaration name'
       , exceptionDeclaration super name' ]

{-| Defines a new data type suitable for use as a concrete exception.  For
example,

>   dataDeclaration (mkName "Name")
> ======>
>   data Name = Name
>             deriving (Show, Typeable) -}
dataDeclaration :: Name -> DecsQ
dataDeclaration name =
  one $ dataD (cxt []) name []
              [normalC name []]
              [''Show, ''Typeable]


----------------------------------- Utility -----------------------------------

-- | Lifts 'DecQ' to a singleton 'DecsQ'.
one :: DecQ -> DecsQ
one = liftM (:[])

-- | Concatenates multiple 'DecsQ' values.
many :: [DecsQ] -> DecsQ
many = liftM concat . sequence

-- | Like 'instanceD', but accepts a 'DecsQ' instead of a '[DecQ]'.
instanceD' :: CxtQ -> TypeQ -> DecsQ -> DecQ
instanceD' c t mkDecs = do
  decs <- mkDecs
  instanceD c t $ map return decs

-- | Unwraps a single-field constructor.
destruct1 :: Name -> ExpQ
destruct1 name = do
  underlying <- newName "underlying"
  lam1E (conP name [varP underlying]) (varE underlying)
