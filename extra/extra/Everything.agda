------------------------------------------------------------------------
-- The Agda standard library
--
-- All library modules, along with short descriptions
------------------------------------------------------------------------

-- Note that core modules are not included.

module Everything where

-- Definitions of algebraic structures like monoids and rings
-- (packed in records together with sets, operations, etc.)
open import Algebra

-- Solver for equations in commutative monoids
open import Algebra.CommutativeMonoidSolver

-- An example of how Algebra.CommutativeMonoidSolver can be used
open import Algebra.CommutativeMonoidSolver.Example

-- Properties of functions, such as associativity and commutativity
open import Algebra.FunctionProperties

-- Relations between properties of functions, such as associativity and
-- commutativity
open import Algebra.FunctionProperties.Consequences

-- Solver for equations in commutative monoids
open import Algebra.IdempotentCommutativeMonoidSolver

-- An example of how Algebra.IdempotentCommutativeMonoidSolver can be
-- used
open import Algebra.IdempotentCommutativeMonoidSolver.Example

-- Solver for monoid equalities
open import Algebra.Monoid-solver

-- Morphisms between algebraic structures
open import Algebra.Morphism

-- Some defined operations (multiplication by natural number and
-- exponentiation)
open import Algebra.Operations

-- Some derivable properties
open import Algebra.Properties.AbelianGroup

-- Some derivable properties
open import Algebra.Properties.BooleanAlgebra

-- Boolean algebra expressions
open import Algebra.Properties.BooleanAlgebra.Expression

-- Some derivable properties
open import Algebra.Properties.DistributiveLattice

-- Some derivable properties
open import Algebra.Properties.Group

-- Some derivable properties
open import Algebra.Properties.Lattice

-- Some derivable properties
open import Algebra.Properties.Ring

-- Solver for commutative ring or semiring equalities
open import Algebra.RingSolver

-- Commutative semirings with some additional structure ("almost"
-- commutative rings), used by the ring solver
open import Algebra.RingSolver.AlmostCommutativeRing

-- Some boring lemmas used by the ring solver
open import Algebra.RingSolver.Lemmas

-- Instantiates the ring solver, using the natural numbers as the
-- coefficient "ring"
open import Algebra.RingSolver.Natural-coefficients

-- Instantiates the ring solver with two copies of the same ring with
-- decidable equality
open import Algebra.RingSolver.Simple

-- Some algebraic structures (not packed up with sets, operations,
-- etc.)
open import Algebra.Structures

-- Applicative functors
open import Category.Applicative

-- Indexed applicative functors
open import Category.Applicative.Indexed

-- Applicative functors on indexed sets (predicates)
open import Category.Applicative.Predicate

-- Functors
open import Category.Functor

-- The identity functor
open import Category.Functor.Identity

-- Functors on indexed sets (predicates)
open import Category.Functor.Predicate

-- Monads
open import Category.Monad

-- A delimited continuation monad
open import Category.Monad.Continuation

-- The identity monad
open import Category.Monad.Identity

-- Indexed monads
open import Category.Monad.Indexed

-- The partiality monad
open import Category.Monad.Partiality

-- An All predicate for the partiality monad
open import Category.Monad.Partiality.All

-- Monads on indexed sets (predicates)
open import Category.Monad.Predicate

-- The state monad
open import Category.Monad.State

-- Basic types related to coinduction
open import Coinduction

-- AVL trees
open import Data.AVL

-- Types and functions which are used to keep track of height
-- invariants in AVL Trees
open import Data.AVL.Height

-- Indexed AVL trees
open import Data.AVL.Indexed

-- Finite maps with indexed keys and values, based on AVL trees
open import Data.AVL.IndexedMap

-- Keys for AVL trees
-- The key type extended with a new minimum and maximum.
open import Data.AVL.Key

-- Finite sets, based on AVL trees
open import Data.AVL.Sets

-- A binary representation of natural numbers
open import Data.Bin

-- Properties of the binary representation of natural numbers
open import Data.Bin.Properties

-- Booleans
open import Data.Bool

-- The type for booleans and some operations
open import Data.Bool.Base

-- A bunch of properties
open import Data.Bool.Properties

-- Showing booleans
open import Data.Bool.Show

-- Bounded vectors
open import Data.BoundedVec

-- Bounded vectors (inefficient, concrete implementation)
open import Data.BoundedVec.Inefficient

-- Characters
open import Data.Char

-- Basic definitions for Characters
open import Data.Char.Base

-- "Finite" sets indexed on coinductive "natural" numbers
open import Data.Cofin

-- Coinductive lists
open import Data.Colist

-- Infinite merge operation for coinductive lists
open import Data.Colist.Infinite-merge

-- Coinductive "natural" numbers
open import Data.Conat

-- Containers, based on the work of Abbott and others
open import Data.Container

-- Properties related to ◇
open import Data.Container.Any

-- Container combinators
open import Data.Container.Combinator

-- The free monad construction on containers
open import Data.Container.FreeMonad

-- Indexed containers aka interaction structures aka polynomial
-- functors. The notation and presentation here is closest to that of
-- Hancock and Hyvernat in "Programming interfaces and basic topology"
-- (2006/9).
open import Data.Container.Indexed

-- Indexed container combinators
open import Data.Container.Indexed.Combinator

-- The free monad construction on indexed containers
open import Data.Container.Indexed.FreeMonad

-- Coinductive vectors
open import Data.Covec

-- Lists with fast append
open import Data.DifferenceList

-- Natural numbers with fast addition (for use together with
-- DifferenceVec)
open import Data.DifferenceNat

-- Vectors with fast append
open import Data.DifferenceVec

-- Digits and digit expansions
open import Data.Digit

-- Empty type
open import Data.Empty

-- An irrelevant version of ⊥-elim
open import Data.Empty.Irrelevant

-- Finite sets
open import Data.Fin

-- Decision procedures for finite sets and subsets of finite sets
open import Data.Fin.Dec

-- Properties related to Fin, and operations making use of these
-- properties (or other properties not available in Data.Fin)
open import Data.Fin.Properties

-- Subsets of finite sets
open import Data.Fin.Subset

-- Some properties about subsets
open import Data.Fin.Subset.Properties

-- Substitutions
open import Data.Fin.Substitution

-- An example of how Data.Fin.Substitution can be used: a definition
-- of substitution for the untyped λ-calculus, along with some lemmas
open import Data.Fin.Substitution.Example

-- Substitution lemmas
open import Data.Fin.Substitution.Lemmas

-- Application of substitutions to lists, along with various lemmas
open import Data.Fin.Substitution.List

-- Floats
open import Data.Float

-- Directed acyclic multigraphs
open import Data.Graph.Acyclic

-- Integers
open import Data.Integer

-- Properties related to addition of integers
open import Data.Integer.Addition.Properties

-- Integers, basic types and operations
open import Data.Integer.Base

-- Divisibility and coprimality
open import Data.Integer.Divisibility

-- Properties related to multiplication of integers
open import Data.Integer.Multiplication.Properties

-- Some properties about integers
open import Data.Integer.Properties

-- Lists
open import Data.List

-- Lists where all elements satisfy a given property
open import Data.List.All

-- Properties related to All
open import Data.List.All.Properties

-- Lists where at least one element satisfies a given property
open import Data.List.Any

-- Properties related to bag and set equality
open import Data.List.Any.BagAndSetEquality

-- List membership and some related definitions
open import Data.List.Any.Membership

-- Properties related to propositional list membership
open import Data.List.Any.Membership.Properties

-- Data.List.Any.Membership instantiated with propositional equality,
-- along with some additional definitions.
open import Data.List.Any.Membership.Propositional

-- Properties related to propositional list membership
open import Data.List.Any.Membership.Propositional.Properties

-- Properties related to Any
open import Data.List.Any.Properties

-- Lists, basic types and operations
open import Data.List.Base

-- A categorical view of List
open import Data.List.Categorical

-- A data structure which keeps track of an upper bound on the number
-- of elements /not/ in a given list
open import Data.List.Countdown

-- Non-empty lists
open import Data.List.NonEmpty

-- Properties of non-empty lists
open import Data.List.NonEmpty.Properties

-- List-related properties
open import Data.List.Properties

-- Lexicographic ordering of lists
open import Data.List.Relation.NonStrictLex

-- Pointwise lifting of relations to lists
open import Data.List.Relation.Pointwise

-- Lexicographic ordering of lists
open import Data.List.Relation.StrictLex

-- Reverse view
open import Data.List.Reverse

-- M-types (the dual of W-types)
open import Data.M

-- Indexed M-types (the dual of indexed W-types aka Petersson-Synek
-- trees).
open import Data.M.Indexed

-- The Maybe type
open import Data.Maybe

-- The Maybe type and some operations
open import Data.Maybe.Base

-- Natural numbers
open import Data.Nat

-- Natural numbers, basic types and operations
open import Data.Nat.Base

-- Coprimality
open import Data.Nat.Coprimality

-- Integer division
open import Data.Nat.DivMod

-- Divisibility
open import Data.Nat.Divisibility

-- Greatest common divisor
open import Data.Nat.GCD

-- Boring lemmas used in Data.Nat.GCD and Data.Nat.Coprimality
open import Data.Nat.GCD.Lemmas

-- A generalisation of the arithmetic operations
open import Data.Nat.GeneralisedArithmetic

-- Definition of and lemmas related to "true infinitely often"
open import Data.Nat.InfinitelyOften

-- Least common multiple
open import Data.Nat.LCM

-- Primality
open import Data.Nat.Primality

-- A bunch of properties about natural number operations
open import Data.Nat.Properties

-- A bunch of properties about natural number operations
open import Data.Nat.Properties.Simple

-- Showing natural numbers
open import Data.Nat.Show

-- Transitive closures
open import Data.Plus

-- Products
open import Data.Product

-- N-ary products
open import Data.Product.N-ary

-- Properties of products
open import Data.Product.Properties

-- Lexicographic products of binary relations
open import Data.Product.Relation.NonStrictLex

-- Pointwise products of binary relations
open import Data.Product.Relation.Pointwise

-- Pointwise lifting of binary relations to sigma types
open import Data.Product.Relation.SigmaPointwise

-- Lexicographic products of binary relations
open import Data.Product.Relation.StrictLex

-- Rational numbers
open import Data.Rational

-- Properties of Rational numbers
open import Data.Rational.Properties

-- Reflexive closures
open import Data.ReflexiveClosure

-- Signs
open import Data.Sign

-- Some properties about signs
open import Data.Sign.Properties

-- The reflexive transitive closures of McBride, Norell and Jansson
open import Data.Star

-- Bounded vectors (inefficient implementation)
open import Data.Star.BoundedVec

-- Decorated star-lists
open import Data.Star.Decoration

-- Environments (heterogeneous collections)
open import Data.Star.Environment

-- Finite sets defined in terms of Data.Star
open import Data.Star.Fin

-- Lists defined in terms of Data.Star
open import Data.Star.List

-- Natural numbers defined in terms of Data.Star
open import Data.Star.Nat

-- Pointers into star-lists
open import Data.Star.Pointer

-- Some properties related to Data.Star
open import Data.Star.Properties

-- Vectors defined in terms of Data.Star
open import Data.Star.Vec

-- Streams
open import Data.Stream

-- Strings
open import Data.String

-- Strings
open import Data.String.Base

-- Sums (disjoint unions)
open import Data.Sum

-- Properties of sums (disjoint unions)
open import Data.Sum.Properties

-- Sums of binary relations
open import Data.Sum.Relation.General

-- Fixed-size tables of values, implemented as functions from 'Fin n'.
-- Similar to 'Data.Vec', but focusing on ease of retrieval instead of
-- ease of adding and removing elements.
open import Data.Table

-- Tables, basic types and operations
open import Data.Table.Base

-- Table-related properties
open import Data.Table.Properties

-- Pointwise table equality
open import Data.Table.Relation.Equality

-- Some unit types
open import Data.Unit

-- The unit type and the total relation on unit
open import Data.Unit.Base

-- Some unit types
open import Data.Unit.NonEta

-- Vectors
open import Data.Vec

-- Vectors where all elements satisfy a given property
open import Data.Vec.All

-- Properties related to All
open import Data.Vec.All.Properties

-- A categorical view of Vec
open import Data.Vec.Categorical

-- Code for converting Vec A n → B to and from n-ary functions
open import Data.Vec.N-ary

-- Some Vec-related properties
open import Data.Vec.Properties

-- Semi-heterogeneous vector equality
open import Data.Vec.Relation.Equality

-- Extensional pointwise lifting of relations to vectors
open import Data.Vec.Relation.ExtensionalPointwise

-- Inductive pointwise lifting of relations to vectors
open import Data.Vec.Relation.InductivePointwise

-- W-types
open import Data.W

-- Indexed W-types aka Petersson-Synek trees
open import Data.W.Indexed

-- Machine words
open import Data.Word

-- Type(s) used (only) when calling out to Haskell via the FFI
open import Foreign.Haskell

-- Simple combinators working solely on and with functions
open import Function

-- Bijections
open import Function.Bijection

-- Function setoids and related constructions
open import Function.Equality

-- Equivalence (coinhabitance)
open import Function.Equivalence

-- Injections
open import Function.Injection

-- Inverses
open import Function.Inverse

-- Left inverses
open import Function.LeftInverse

-- A universe which includes several kinds of "relatedness" for sets,
-- such as equivalences, surjections and bijections
open import Function.Related

-- Basic lemmas showing that various types are related (isomorphic or
-- equivalent or…)
open import Function.Related.TypeIsomorphisms

-- Surjections
open import Function.Surjection

-- IO
open import IO

-- Primitive IO: simple bindings to Haskell types and functions
open import IO.Primitive

-- An abstraction of various forms of recursion/induction
open import Induction

-- Lexicographic induction
open import Induction.Lexicographic

-- Various forms of induction for natural numbers
open import Induction.Nat

-- Well-founded induction
open import Induction.WellFounded

-- Universe levels
open import Level

-- Record types with manifest fields and "with", based on Randy
-- Pollack's "Dependently Typed Records in Type Theory"
open import Record

-- Support for reflection
open import Reflection

-- Properties of homogeneous binary relations
open import Relation.Binary

-- Some properties imply others
open import Relation.Binary.Consequences

-- Convenient syntax for equational reasoning
open import Relation.Binary.EqReasoning

-- Equivalence closures of binary relations
open import Relation.Binary.EquivalenceClosure

-- Many properties which hold for _∼_ also hold for flip _∼_
open import Relation.Binary.Flip

-- Heterogeneous equality
open import Relation.Binary.HeterogeneousEquality

-- Quotients for Heterogeneous equality
open import Relation.Binary.HeterogeneousEquality.Quotients

-- Example of a Quotient: ℤ as (ℕ × ℕ / ~)
open import Relation.Binary.HeterogeneousEquality.Quotients.Examples

-- Indexed binary relations
open import Relation.Binary.Indexed

-- Induced preorders
open import Relation.Binary.InducedPreorders

-- Order-theoretic lattices
open import Relation.Binary.Lattice

-- Lexicographic ordering of lists
open import Relation.Binary.List.NonStrictLex

-- Pointwise lifting of relations to lists
open import Relation.Binary.List.Pointwise

-- Lexicographic ordering of lists
open import Relation.Binary.List.StrictLex

-- Conversion of ≤ to <, along with a number of properties
open import Relation.Binary.NonStrictToStrict

-- Many properties which hold for _∼_ also hold for _∼_ on f
open import Relation.Binary.On

-- Order morphisms
open import Relation.Binary.OrderMorphism

-- Convenient syntax for "equational reasoning" using a partial order
open import Relation.Binary.PartialOrderReasoning

-- Convenient syntax for "equational reasoning" using a preorder
open import Relation.Binary.PreorderReasoning

-- Lexicographic products of binary relations
open import Relation.Binary.Product.NonStrictLex

-- Pointwise products of binary relations
open import Relation.Binary.Product.Pointwise

-- Lexicographic products of binary relations
open import Relation.Binary.Product.StrictLex

-- Properties satisfied by bounded join semilattices
open import Relation.Binary.Properties.BoundedJoinSemilattice

-- Properties satisfied by bounded meet semilattices
open import Relation.Binary.Properties.BoundedMeetSemilattice

-- Properties satisfied by decidable total orders
open import Relation.Binary.Properties.DecTotalOrder

-- Properties satisfied by join semilattices
open import Relation.Binary.Properties.JoinSemilattice

-- Properties satisfied by lattices
open import Relation.Binary.Properties.Lattice

-- Properties satisfied by meet semilattices
open import Relation.Binary.Properties.MeetSemilattice

-- Properties satisfied by posets
open import Relation.Binary.Properties.Poset

-- Properties satisfied by preorders
open import Relation.Binary.Properties.Preorder

-- Properties satisfied by strict partial orders
open import Relation.Binary.Properties.StrictPartialOrder

-- Properties satisfied by strict partial orders
open import Relation.Binary.Properties.StrictTotalOrder

-- Properties satisfied by total orders
open import Relation.Binary.Properties.TotalOrder

-- Propositional (intensional) equality
open import Relation.Binary.PropositionalEquality

-- An equality postulate which evaluates
open import Relation.Binary.PropositionalEquality.TrustMe

-- Helpers intended to ease the development of "tactics" which use
-- proof by reflection
open import Relation.Binary.Reflection

-- Convenient syntax for "equational reasoning" in multiple Setoids
open import Relation.Binary.SetoidReasoning

-- Pointwise lifting of binary relations to sigma types
open import Relation.Binary.Sigma.Pointwise

-- Some simple binary relations
open import Relation.Binary.Simple

-- Convenient syntax for "equational reasoning" using a strict partial
-- order
open import Relation.Binary.StrictPartialOrderReasoning

-- Conversion of < to ≤, along with a number of properties
open import Relation.Binary.StrictToNonStrict

-- Sums of binary relations
open import Relation.Binary.Sum

-- Symmetric closures of binary relations
open import Relation.Binary.SymmetricClosure

-- Pointwise lifting of relations to vectors
open import Relation.Binary.Vec.Pointwise

-- Operations on nullary relations (like negation and decidability)
open import Relation.Nullary

-- Operations on and properties of decidable relations
open import Relation.Nullary.Decidable

-- Implications of nullary relations
open import Relation.Nullary.Implication

-- Properties related to negation
open import Relation.Nullary.Negation

-- Products of nullary relations
open import Relation.Nullary.Product

-- Sums of nullary relations
open import Relation.Nullary.Sum

-- A universe of proposition functors, along with some properties
open import Relation.Nullary.Universe

-- Unary relations
open import Relation.Unary

-- Predicate transformers
open import Relation.Unary.PredicateTransformer

-- Sizes for Agda's sized types
open import Size

-- Strictness combinators
open import Strict

-- Universes
open import Universe

