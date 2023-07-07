// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

duchess::java_package! {
    package java.io;
    class PrintStream {}
    class PrintWriter {}
    class StringWriter {}

    package java.lang;
    class Class {}
    class Object {
        public java.lang.String toString();
    }

    package java.math;
    class BigInteger {}

    package java.nio.file;
    class Paths {}

    package scala;
    class "None$" extends scala.Option<scala.runtime."Nothing$"> {
        public static scala."None$" "MODULE$";
    }
    class AnyVal { * }
    class Function1 {}
    class Option<A> {}
    class Product {}
    class Some<A> extends scala.Option<A> {}
    class Tuple2<T1, T2> {}

    package scala.runtime;
    class "Nothing$" {}

    package scala.collection;
    interface IterableOnceOps<A, CC, C> {
        default scala.collection.immutable.Seq<A> toSeq();
    }
    interface IterableOps<A, CC, C> extends scala.collection.IterableOnceOps<A, CC, C> {}
    interface SeqOps<A, CC, C> extends scala.collection.IterableOps<A, CC, C> {}
    interface StrictOptimizedSeqOps<A, CC, C> extends scala.collection.SeqOps<A, CC, C> {}

    package scala.collection.immutable;
    interface Map<K, V> {}
    interface Seq<A> {}

    package scala.collection.mutable;
    class ArrayBuffer<A> implements scala.collection.StrictOptimizedSeqOps<
        A, scala.collection.mutable.ArrayBuffer, scala.collection.mutable.ArrayBuffer<A>
    > {
        public scala.collection.mutable.ArrayBuffer();
    }

    package viper.silver.ast;
    class "AbstractAssign$" {}
    class "BackendFuncApp$" {}
    class "Bool$" {}
    class "DomainFuncApp$" {}
    class "Int$" {}
    class "NoInfo$" implements viper.silver.ast.Info {
        public static viper.silver.ast."NoInfo$" "MODULE$";
    }
    class "NoPosition$" implements viper.silver.ast.Position {
        public static viper.silver.ast."NoPosition$" "MODULE$";
    }
    class "NoTrafos$" implements viper.silver.ast.ErrorTrafo {
        public static viper.silver.ast."NoTrafos$" "MODULE$";
    }
    class "Perm$" {}
    class "Ref$" {}
    class "Wand$" {}
    class Add {}
    class And {}
    class AnnotationInfo {}
    class AnySetCardinality {}
    class AnySetContains {}
    class AnySetIntersection {}
    class AnySetMinus {}
    class AnySetSubset {}
    class AnySetUnion {}
    class Apply {}
    class Applying {}
    class Assert {}
    class Bool {}
    class CondExp {}
    class CurrentPerm {}
    class Declaration {}
    class Div {}
    class Domain {}
    class DomainFunc {}
    class DomainFuncApp {}
    class DomainType {}
    class EmptyMap {}
    class EmptyMultiset {}
    class EmptySeq {}
    class EmptySet {}
    class EpsilonPerm {}
    class EqCmp {}
    class Exhale {}
    class Exists {}
    class Exp {}
    class ExplicitMap {}
    class ExplicitMultiset {}
    class ExplicitSeq {}
    class ExplicitSet {}
    class ExtensionMember {}
    class FalseLit {}
    class Field {}
    class FieldAccess {}
    class FieldAccessPredicate {}
    class FieldAssign {}
    class Fold {}
    class Forall {}
    class ForPerm {}
    class FractionalPerm {}
    class FullPerm {}
    class FuncApp {}
    class Function {}
    class GeCmp {}
    class Goto {}
    class GtCmp {}
    class IdentifierPosition {}
    class If {}
    class Implies {}
    class Inhale {}
    class InhaleExhaleExp {}
    class Int {}
    class IntLit {}
    class IntPermMul {}
    class Label {}
    class LabelledOld {}
    class LeCmp {}
    class Let {}
    class LineColumnPosition {}
    class LocalVar {}
    class LocalVarAssign {}
    class LocalVarDecl {}
    class Location {}
    class LtCmp {}
    class MagicWand {}
    class MapCardinality {}
    class MapContains {}
    class MapLookup {}
    class MapType {}
    class MapUpdate {}
    class Method {}
    class MethodCall {}
    class Minus {}
    class Mod {}
    class Mul {}
    class MultisetType {}
    class NamedDomainAxiom {}
    class NeCmp {}
    class NewStmt {}
    class NoPerm {}
    class Not {}
    class NullLit {}
    class Old {}
    class Or {}
    class Package {}
    class PermAdd {}
    class PermDiv {}
    class PermGeCmp {}
    class PermGtCmp {}
    class PermLeCmp {}
    class PermLtCmp {}
    class PermMinus {}
    class PermMul {}
    class PermSub {}
    class Predicate {}
    class PredicateAccess {}
    class PredicateAccessPredicate {}
    class Program {
        public viper.silver.ast.Program(
            scala.collection.immutable.Seq<viper.silver.ast.Domain>,
            scala.collection.immutable.Seq<viper.silver.ast.Field>,
            scala.collection.immutable.Seq<viper.silver.ast.Function>,
            scala.collection.immutable.Seq<viper.silver.ast.Predicate>,
            scala.collection.immutable.Seq<viper.silver.ast.Method>,
            scala.collection.immutable.Seq<viper.silver.ast.ExtensionMember>,
            viper.silver.ast.Position,
            viper.silver.ast.Info,
            viper.silver.ast.ErrorTrafo
        );
    }
    class RangeSeq {}
    class Result {}
    class SeqAppend {}
    class SeqContains {}
    class SeqDrop {}
    class SeqIndex {}
    class SeqLength {}
    class Seqn {}
    class SeqTake {}
    class SeqType {}
    class SeqUpdate {}
    class SetType {}
    class SimpleInfo {
        public viper.silver.ast.SimpleInfo(scala.collection.immutable.Seq<java.lang.String>);
    }
    class Stmt {}
    class Sub {}
    class Trigger {}
    class TrueLit {}
    class Type {}
    class TypeVar {}
    class Unfold {}
    class Unfolding {}
    class While {}
    class WildcardPerm {}
    interface ErrorTrafo {}
    interface Info {}
    interface Position {}

    package viper.silver.plugin.standard.refute;
    class Refute {}

    package viper.silver.frontend;
    class SilFrontend {}

    package viper.silver.verifier;
    interface Verifier {}

    package viper.silver.reporter;
    class "NoopReporter$" implements viper.silver.reporter.Reporter {
        public static viper.silver.reporter."NoopReporter$" "MODULE$";
    }
    interface Reporter {}

    package viper.silver.ast.utility;
    class "Simplifier$" {}
    class BVFactory {}
    class FloatFactory {}
    class RoundingMode {}

    package viper.silicon;
    class Silicon {
        public viper.silicon.Silicon();
    }

    package viper.carbon;
    class CarbonVerifier implements viper.silver.verifier.Verifier {
        public viper.carbon.CarbonVerifier(
            viper.silver.reporter.Reporter,
            scala.collection.immutable.Seq<scala.Tuple2<java.lang.String, java.lang.Object>>
        );
    }
}
