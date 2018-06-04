// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

extern crate env_logger;
extern crate error_chain;
extern crate jni_gen;
extern crate reqwest;
extern crate tempdir;

use std::fs;
use std::env;
use jni_gen::*;
use error_chain::ChainedError;
use std::io::copy;
use std::fs::File;
use tempdir::TempDir;

fn main() {
    env_logger::init().expect("failed to initialize env_logger");
    let generated_dir = format!("{}/gen", env::var("CARGO_MANIFEST_DIR").unwrap());

    let deps_dir = TempDir::new("deps").unwrap_or_else(|e| {
        panic!(e.to_string());
    });

    // If ASM_JAR is set, use it. Otherwise, download asm.jar to a temporary location.
    let asm_jar = match env::var("ASM_JAR").ok() {
        Some(location) => location,
        None => {
            let target = "http://central.maven.org/maven2/asm/asm/3.3.1/asm-3.3.1.jar";
            let mut response = reqwest::get(target).unwrap_or_else(|e| {
                panic!(e.to_string());
            });
            let fname = deps_dir.path().join("asm.jar");
            let mut dest = File::create(fname.clone()).unwrap_or_else(|e| {
                panic!(e.to_string());
            });
            copy(&mut response, &mut dest).unwrap_or_else(|e| {
                panic!(e.to_string());
            });
            fname.to_str().unwrap().to_string()
        }
    };

    let mut viper_jars: Vec<String> = fs::read_dir("/usr/lib/viper/")
        .unwrap()
        .map(|x| x.unwrap().path().to_str().unwrap().to_string())
        .collect();

    WrapperGenerator::new()
        .use_jar(&asm_jar)
        .use_jars(&mut viper_jars)
        .wrap_all(vec![
            // Java
            java_class!("java.io.PrintStream", vec![
                constructor!("(Ljava/io/OutputStream;)V"),
                method!("println", "(Ljava/lang/Object;)V")
            ]),
            java_class!("java.io.PrintWriter", vec![
                constructor!("(Ljava/io/Writer;)V"),
            ]),
            java_class!("java.io.StringWriter", vec![
                constructor!("()V"),
            ]),
            java_class!("java.lang.Class", vec![
                method!("getName"),
            ]),
            java_class!("java.lang.Object", vec![
                constructor!(),
                method!("toString"),
            ]),
            java_class!("java.lang.System", vec![
                method!("getProperty", "(Ljava/lang/String;)Ljava/lang/String;"),
            ]),
            java_class!("java.lang.Throwable", vec![
                method!("printStackTrace", "(Ljava/io/PrintWriter;)V")
            ]),
            java_class!("java.math.BigInteger", vec![
                constructor!("(Ljava/lang/String;)V"),
            ]),
            java_class!("java.nio.file.Paths", vec![
                method!("get", "(Ljava/lang/String;[Ljava/lang/String;)Ljava/nio/file/Path;"),
            ]),
            // Scala
            java_class!("scala.Some", vec![
                constructor!(),
            ]),
            java_class!("scala.None$", vec![
                object_getter!(),
            ]),
            java_class!("scala.Predef", vec![
                method!("wrapRefArray"),
            ]),
            java_class!("scala.math.BigInt", vec![
                constructor!(),
            ]),
            java_class!("scala.collection.mutable.ArraySeq", vec![
                constructor!(),
                method!("update"),
            ]),
            java_class!("scala.collection.mutable.ListBuffer", vec![
                constructor!(),
            ]),
            java_class!("scala.collection.immutable.HashMap", vec![
                constructor!(),
                method!("updated", "(Ljava/lang/Object;Ljava/lang/Object;)Lscala/collection/immutable/HashMap;"),
            ]),
            java_class!("scala.collection.Seq", vec![
                method!("length"),
                method!("apply", "(I)Ljava/lang/Object;"),
                method!("toArray"),
            ]),
            java_class!("scala.reflect.ClassTag$", vec![
                object_getter!(),
                method!("apply"),
            ]),
            // Viper
            java_class!("viper.silicon.interfaces.Failure", vec![
                constructor!(),
            ]),
            java_class!("viper.silicon.Silicon", vec![
                constructor!("()V"),
                method!("name"),
                method!("buildVersion"),
                method!("parseCommandLine"),
                method!("start"),
                method!("stop"),
                method!("verify"),
            ]),
            java_class!("viper.silver.ast.pretty.FastPrettyPrinter$", vec![
                object_getter!(),
                method!("pretty", "(Lviper/silver/ast/Node;)Ljava/lang/String;")
            ]),
            java_class!("viper.silver.ast.AbstractAssign$", vec![
                object_getter!(),
                method!("apply"),
            ]),
            java_class!("viper.silver.ast.Add", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.AddOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.And", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.AndOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.AnySetContains", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.AnySetUnion", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.AnySetIntersection", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.AnySetSubset", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.AnySetMinus", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.AnySetCardinality", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Apply", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Applying", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Assert", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Bool$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.CondExp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Constraining", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.CurrentPerm", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Div", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.DivOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Domain", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.DomainAxiom", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.DomainFunc", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.DomainFuncApp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.DomainFuncApp$", vec![
                object_getter!(),
                method!("apply", "(Lviper/silver/ast/DomainFunc;Lscala/collection/Seq;Lscala/collection/immutable/Map;Lviper/silver/ast/Position;Lviper/silver/ast/Info;Lviper/silver/ast/ErrorTrafo;)Lviper/silver/ast/DomainFuncApp;"),
            ]),
            java_class!("viper.silver.ast.DomainType", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.EmptySeq", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.EmptyMultiset", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.EmptySet", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.EpsilonPerm", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.EqCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Exhale", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Exists", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.ExplicitMultiset", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.ExplicitSeq", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.ExplicitSet", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.FalseLit", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Field", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.FieldAccess", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.FieldAccessPredicate", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.FieldAssign", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Fold", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Forall", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.ForPerm", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.FracOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.FractionalPerm", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Fresh", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.FullPerm", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.FuncApp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.FuncApp$", vec![
                object_getter!(),
                method!("apply", "(Lviper/silver/ast/Function;Lscala/collection/Seq;Lviper/silver/ast/Position;Lviper/silver/ast/Info;Lviper/silver/ast/ErrorTrafo;)Lviper/silver/ast/FuncApp;"),
            ]),
            java_class!("viper.silver.ast.Function", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.GeCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.GeOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Goto", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.GtCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.GtOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.HasIdentifier", vec![
                method!("id"),
            ]),
            java_class!("viper.silver.ast.IdentifierPosition", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.If", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Implies", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.ImpliesOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Inhale", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.InhaleExhaleExp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Int$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.IntLit", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.IntPermMul", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.IntPermMulOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Label", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LabelledOld", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LeCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LeOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Let", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LineColumnPosition", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LocalVar", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LocalVarAssign", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LocalVarDecl", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LocalVarDeclStmt", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LtCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.LtOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.MagicWand", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Method", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.MethodCall", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Minus", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Mod", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.ModOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Mul", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.MulOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.MultisetType", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.NeCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.NegOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.NewStmt", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Node", vec![
                method!("checkTransitively")
            ]),
            java_class!("viper.silver.ast.NoInfo$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.NoPerm", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.NoPosition$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Not", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.NotOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.NoTrafos$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.NullLit", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Old", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Or", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.OrOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Package", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Perm$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.PermAdd", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PermAddOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.PermDivOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.PermGeCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PermGtCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PermLeCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PermLtCmp", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PermMinus", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PermMul", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PermSub", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PermDiv", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Predicate", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PredicateAccess", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.PredicateAccessPredicate", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Program", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.RangeSeq", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Ref$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Result", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SeqAppend", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SeqContains", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SeqDrop", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SeqIndex", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SeqLength", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Seqn", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SeqTake", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SeqType", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SeqUpdate", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SetType", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SimpleInfo", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Sub", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.SubOp$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Trigger", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.TrueLit", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.TypeVar", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Unfold", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.Unfolding", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.utility.QuantifiedPermissions$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.Wand$", vec![
                object_getter!(),
            ]),
            java_class!("viper.silver.ast.While", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.ast.WildcardPerm", vec![
                constructor!(),
            ]),
            java_class!("viper.silver.verifier.AbortedExceptionally", vec![
                constructor!(),
                method!("cause"),
            ]),
            java_class!("viper.silver.verifier.ErrorMessage", vec![
            ]),
            java_class!("viper.silver.verifier.Failure", vec![
                constructor!(),
                method!("errors"),
            ]),
            java_class!("viper.silver.verifier.AbstractError", vec![
            ]),
            java_class!("viper.silver.verifier.VerificationError", vec![
                method!("id"),
                method!("pos"),
                method!("fullId"),
                method!("reason"),
                method!("readableMessage", "()Ljava/lang/String;"),
            ]),
            java_class!("viper.silver.verifier.ConsistencyError", vec![
                constructor!(),
            ]),
        ])
        .generate(&generated_dir)
        .unwrap_or_else(|e| {
            panic!(e.display_chain().to_string());
        });

    // Remove the temporary directory
    drop(deps_dir);
}
