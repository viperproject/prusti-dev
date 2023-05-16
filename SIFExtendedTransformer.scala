// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.silver.sif

import viper.silver.ast._
import viper.silver.ast.utility.Simplifier
import viper.silver.verifier.errors
import viper.silver.verifier.errors.{AssertFailed, ErrorNode}

import scala.collection.immutable.HashSet
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

trait SIFExtendedTransformer {
  object Config {
    /** If true, don't generate all the control flow variables, just the ones needed for each method. */
    var optimizeControlFlow: Boolean = true
    /** If true, try to bunch as many statements into a single if statement which was introduced for checking active
      * executions, instead of having one if stmt per original statement. */
    var optimizeSequential: Boolean = true
    /** If true, add an 'assume p1' at the beginning of each method, to cut down on redundant paths the
      * verification could consider */
    var optimizeRestrictActVars: Boolean = true
    /** Applications of the functions which have an entry here, will be replaced by the expression
      * determined by the entry in the second execution. */
    var primedFuncAppReplacements: mutable.HashMap[String, (FuncApp, Exp, Exp) => Exp] = new mutable.HashMap
    /** Set this to only transform methods that contain relational assertions somewhere in their spec or body.
      * May lead to invalid programs when such a method calls another methods that does contain such specs.
      */
    var onlyTransformMethodsWithRelationalSpecs: Boolean = false
    var generateAllLowFuncs: Boolean = true
  }
  def optimizeControlFlow(v: Boolean): Unit = {
    Config.optimizeControlFlow = v
  }
  def optimizeSequential(v: Boolean): Unit = {
    Config.optimizeSequential = v
  }
  def optimizeRestrictActVars(v: Boolean): Unit = {
    Config.optimizeRestrictActVars = v
  }
  def generateAllLowFuncs(v: Boolean): Unit = {
    Config.generateAllLowFuncs = v
  }
  def onlyTransformMethodsWithRelationalSpecs(v: Boolean): Unit = {
    Config.onlyTransformMethodsWithRelationalSpecs = v
  }
  def addPrimedFuncAppReplacement(name: String, strategy: String): Unit = {
    strategy match {
      case "first_arg" => Config.primedFuncAppReplacements.put(name,
        (func, p1, p2) => translatePrime(func.args.head, p1, p2))
      case "true" => Config.primedFuncAppReplacements.put(name, (func, _, _) =>
        TrueLit()(func.pos, func.info, func.errT))
      case _ => new IllegalArgumentException(
        s"""Unknown strategy "$strategy" for primed function application replacement.""")
    }
  }
  def clearPrimedFuncAppReplacement(): Unit = {
    Config.primedFuncAppReplacements.clear()
  }

  val primedNamesPerMethod = new mutable.HashMap[String, Map[String, String]]
  val primedNames = new mutable.HashMap[String, String]
  val relationalPredicates = new mutable.HashSet[Predicate]
  val predLowFuncs = new mutable.HashMap[String, Option[Function]]
  val predLowFuncInfo = new mutable.HashMap[String, Option[(String, Seq[LocalVarDecl], Seq[LocalVarDecl])]]
  val predAllLowFuncs = new mutable.HashMap[String, Option[Function]]()
  val predAllLowFuncInfo = new mutable.HashMap[String, Option[(String, Seq[LocalVarDecl], Seq[LocalVarDecl])]]
  val usedNames = new mutable.HashSet[String]
  var newFields : List[Field] = Nil
  var newPredicates: Seq[Predicate] = Nil
  var _program : Program = null
  var getArgFunc : DomainFunc = null
  var getOldFunc : DomainFunc = null
  var getArgPFunc : DomainFunc = null
  var getOldPFunc : DomainFunc = null

  private var _allLowMethods: Set[String] = HashSet[String]()
  def allLowMethods: Set[String] = _allLowMethods
  def setAllLowMethods(value: Set[String]): Unit = _allLowMethods = value

  private var _preservesLowMethods: Set[String] = HashSet[String]()
  def preservesLowMethods: Set[String] = _preservesLowMethods
  def setPreservesLowMethods(value: Set[String]): Unit =_preservesLowMethods = value

  private val _domainFuncsToDuplicate = new mutable.HashSet[DomainFunc]()
  def domainFuncsToDuplicate: mutable.Set[DomainFunc] = _domainFuncsToDuplicate
  def addDomainFuncToDuplicate(funcs: DomainFunc*): Unit = _domainFuncsToDuplicate ++= funcs

  var timing = false
  var time : Option[LocalVar] = None

  val skip: Seqn = Seqn(Seq(), Seq())()

  def transform(p: Program, enableTiming: Boolean) : Program = {
    primedNames.clear()
    predLowFuncs.clear()
    predLowFuncInfo.clear()
    predAllLowFuncInfo.clear()
    usedNames.clear()
    newPredicates = Nil
    timing = enableTiming
    _program = p

    val allNames = p.collect({
      case d: Declaration => d.name
    })
    usedNames ++= allNames

    collectRelationalPredicates(_program, relationalPredicates)
    createNewNames(p)
    var newFunctions: Seq[Function] = p.functions //.flatMap(f => translateFunction(f))
    newPredicates = Seq()
    for (pred <- p.predicates) {
      val (newPs, predFuncs) = translatePredicate(pred)
      newPredicates ++= newPs
      newFunctions ++= predFuncs.collect{case f if f.isDefined => f.get}
    }

    val newMethods: Seq[Method] = if (Config.onlyTransformMethodsWithRelationalSpecs) {
      val relationalMethods = p.methods.filter(m => m.existsDefined({
        case e: Exp if !isUnary(e) => true
      }))
      val unaryMethods = p.methods.filter(m => !relationalMethods.contains(m))
      relationalMethods.map(m => translateMethod(m)) ++ unaryMethods
    }else{
      p.methods.map(m => translateMethod(m))
    }

    p.copy(functions = newFunctions, predicates = newPredicates,
      methods = newMethods)(p.pos, p.info, p.errT)
  }

  def getName(orig: String) : String = {
    if (usedNames.contains(orig)){
      var index = 0
      while (usedNames.contains(orig + "_" + index)){
        index += 1
      }
      val result = orig + "_" + index
      usedNames.add(result)
      return result
    }else{
      usedNames.add(orig)
      return orig
    }
  }

  /** Create the new names for the programs variables, functions (those which depend on the heap),
    * and predicates, which are used for the second execution. Updates [[primedNames]].
    * @param p The program being encoded.
    */
  def createNewNames(p: Program): Unit = {
    // duplicate names for predicates
    for (pred <- p.predicates) {
      val duplicatedArgs = pred.formalArgs.map{a =>
        val newName = getName(a.name)
        a.copy(name = newName)(a.pos, a.info, a.errT)
      }
      predLowFuncInfo.update(pred.name, if (relationalPredicates.contains(pred) && pred.body.isDefined)
          Some(getName(pred.name + "_low"), pred.formalArgs, duplicatedArgs)
        else None
      )
      predAllLowFuncInfo.update(pred.name, pred.body match {
        case Some(_) =>
          Some(getName(pred.name + "_all_low"), pred.formalArgs, duplicatedArgs)
        case None => None
      })
    }
  }

  def collectRelationalPredicates(p: Program, relPreds: mutable.HashSet[Predicate]): Unit = {
    def directlyRelational(pred: Predicate): Boolean = {
       pred.body.isDefined && !isUnary(pred.body.get)
    }

    relPreds.clear()
    relPreds ++= p.predicates.filter(pred => directlyRelational(pred))
    val dependencies = mutable.HashMap[String, Seq[String]]()

    relPreds.foreach(pred =>
      // put the name of this as depending on all referenced predicates
      pred.body.collect{
        case pap: PredicateAccessPredicate => pap
      }.foreach(pap =>
        dependencies.update(pap.loc.predicateName, dependencies.getOrElse(pap.loc.predicateName, Seq()) :+ pred.name)
      )
    )
    // go through dependent predicates to add them to relationals
    val queue = mutable.Queue[String](relPreds.toSeq.map(rp => rp.name): _*)
    while (queue.nonEmpty) {
      val head: String = queue.dequeue()
      for (dep <- dependencies.getOrElse(head, Seq())) {
        if (relPreds.add(p.findPredicate(dep))) queue.enqueue(dep)
      }
    }
  }

  def translateMethod(m: Method) : Method = {
    val primedBefore = primedNames.clone()
    val (p1d, p1r) = getNewBool("p1")
    val (p2d, p2r) = getNewBool("p2")
    var toAdd = Seq(p1d, p2d)
    val (t1d, t1r) = getNewVar("t1", Int)
    val (t2d, t2r) = getNewVar("t2", Int)
    if (timing){
      toAdd = Seq(p1d, p2d, t1d, t2d)
      primedNames.update(t1d.name, t2d.name)
      time = Some(t1r)
    }

    val newArgs = toAdd ++ m.formalArgs.flatMap{a =>
      val newName = getName(a.name)
      primedNames.update(a.name, newName)
      val primedArg = a.copy(name = newName)(a.pos, a.info, a.errT)
      Seq(a, primedArg)
    }
    var toAddRet : Seq[LocalVarDecl] = Seq()
    val (t1dr, t1rr) = getNewVar("t1", Int)
    val (t2dr, t2rr) = getNewVar("t2", Int)
    if (timing){
      toAddRet = Seq(t1dr, t2dr)
      primedNames.update(t1dr.name, t2dr.name)
      time = Some(t1rr)
    }
    val newReturns = toAddRet ++ m.formalReturns.flatMap{r =>
      val newName = getName(r.name)
      primedNames.update(r.name, newName)
      val primedRet = r.copy(name = newName)(r.pos, r.info, r.errT)
      Seq(r, primedRet)
    }

    var (newPres, newPosts) = addLownessConditions(m, m.pres, m.posts)
    val condCtx = TranslationContext(p1r, p2r, EmptyControlFlowVars(), m)
    newPres = newPres.map{e => translateSIFAss(e, condCtx.copy(translatingPrecond = true))}
    newPosts = newPosts.map{e => translateSIFAss(e, condCtx)}
    // Termination channels
    var terminates: Option[SIFTerminatesExp] = None
    m.pres.foreach(pre => pre.visit{
      case t: SIFTerminatesExp => terminates = Some(t)
    })
    if (terminates.isDefined) {
      newPres = simplifyConditions(newPres ++
        terminationChannelsLowChecks(terminates.get, condCtx))
      newPosts :+= translateSIFAss(Old(terminates.get.cond)(
        terminates.get.cond.pos, terminates.get.cond.info,
        ErrTrafo({case _ => SIFTerminationChannelCheckFailed(terminates.get.cond, SIFTermCondNotTight(terminates.get))})
      ), condCtx)
    }

    if (timing){
      val timeUnchanged1 = Implies(Not(p1r)(), EqCmp(t1r, t1rr)())()
      val timeUnchanged2 = Implies(Not(p2r)(), EqCmp(t2r, t2rr)())()
      newPosts ++= Seq(timeUnchanged1, timeUnchanged2)
    }

    var firstStatements : Seq[Stmt] = Seq()
    if (Config.optimizeRestrictActVars) firstStatements :+= Inhale(p1r)()
    if (timing){
      val assignTime1 = LocalVarAssign(t1rr, t1r)()
      val assignTime2 = LocalVarAssign(t2rr, t2r)()
      firstStatements ++= Seq(assignTime1, assignTime2)
      time = Some(t1rr)
    }

    var newBody: Option[Seqn] = None
    if (m.body.isDefined) {
      var body: Seqn = m.body.get
      if (allLowMethods.contains(m.name) || preservesLowMethods.contains(m.name)) {
        body = inferLowLoopInvariants(m, preservesOnly = preservesLowMethods.contains(m.name))
      }

      // find which control variables the method requires
      val ctrlVars: MethodControlFlowVars = createControlFlowVars(body)
      val ctx: TranslationContext = TranslationContext(p1r, p2r, ctrlVars, m)

      newBody = Some(Seqn(firstStatements ++ ctrlVars.initAssigns() ++
        Seq(translateStatement(body, ctx).asInstanceOf[Seqn]), ctrlVars.declarations())())
    }

    time = None
    primedNamesPerMethod.update(m.name, primedNames.toMap)
    primedNames.clear()
    primedNames ++= primedBefore
    Method(m.name, newArgs, newReturns, newPres, newPosts, newBody)(m.pos)
  }

  def _conjoinOptions(in: Seq[Option[Exp]]): Exp = {
    val defined = in.filter(x => x.isDefined).map(x => x.get)
    defined.size match {
      case 0 => TrueLit()()
      case _ => defined.reduceRight((a, b) => And(a, b)(a.pos))
    }
  }

  /** Takes a sequence of LocalVarDecls and produces an expression saying each pair of adjacent variables are equal.
    */
  def _varDeclsToAllLow(in: Seq[LocalVarDecl]): Exp = {
    in.map(decl => decl.localVar)
      .map(v => SIFLowExp(v, None)())
      .reduceRight[Exp]((v, e) => And(v, e)())
  }

  def allReachableStateLow(m: Method, old: Boolean, predicateSrc: Seq[Exp]): Option[Exp] = {
    var lowExpressions: Seq[Exp] = Seq()

    // all accs to fields in preconditions
    val allFieldAccesses: Seq[FieldAccess] = m.pres.flatMap(e => e.deepCollect({
      case FieldAccessPredicate(loc, _) => Seq(loc)
    })).flatten.distinct
    for (fieldAcc <- allFieldAccesses) {
      val eq = SIFLowExp(fieldAcc, None)(m.pos)
      if (old)
        lowExpressions :+= Old(eq)(m.pos)
      else
        lowExpressions :+= eq
    }

    // all accs we get via predicates
    lowExpressions ++= predicateSrc.flatMap(e => e.deepCollect{
      case PredicateAccessPredicate(loc, _) =>
        val funcApp = FuncApp(predAllLowFuncs(loc.predicateName).get,
          loc.args ++ loc.args.map(a => translatePrime(a, null, null)))()
        if (old)
          Old(funcApp)(m.pos)
        else
          funcApp
    })

    if (lowExpressions.nonEmpty)
      Some(lowExpressions.reduceRight[Exp]((a, b) => And(a, b)(m.pos)))
    else
      None
  }

  def allVarsAndStateLow(m: Method, vars: Seq[LocalVarDecl], old: Boolean, predicateSrc: Seq[Exp]): Exp = {
    val nonObligationVars = vars.filterNot(isObligationVar)
    val allArgsLow: Option[Exp] = if (nonObligationVars.isEmpty) None else Some(_varDeclsToAllLow(nonObligationVars))
    val allStateLow: Option[Exp] = allReachableStateLow(m, old, predicateSrc)
    _conjoinOptions(Seq(allArgsLow, allStateLow))
  }

  def addLownessConditions(m: Method, pres: Seq[Exp], posts: Seq[Exp]): (Seq[Exp], Seq[Exp]) = {
    var newPres = pres
    if (allLowMethods.contains(m.name)) newPres :+= allVarsAndStateLow(m, m.formalArgs, old = false, predicateSrc = m.pres)
    var newPosts = posts
    if (allLowMethods.contains(m.name)) newPosts :+= allVarsAndStateLow(m, m.formalReturns, old = false, predicateSrc = m.posts)
    if (preservesLowMethods.contains(m.name)) newPosts :+= Implies(
      allVarsAndStateLow(m, m.formalArgs, old = true, predicateSrc = m.pres),
      allVarsAndStateLow(m, m.formalReturns, old = false, predicateSrc = m.posts))(m.pos)
    (newPres, newPosts)
  }

  def inferLowLoopInvariants(m: Method, preservesOnly: Boolean): Seqn = {
    val _obligationVars: Seq[String] = obligationVars(m)
    m.body.get.transform{
      case w@While(cond, invs, body) =>
        val targets: Seq[LocalVar] = w.deepCollect({
          case LocalVarAssign(lhs, _) => Seq(lhs)
          case MethodCall(_, _, ts) => ts
          case NewStmt(t, _) => Seq(t)
        }).flatten
          .distinct
          .filterNot(v => _obligationVars.contains(v.name))
        var additionalInvs: Seq[Exp] = targets.map(lv => SIFLowExp(lv, None)()) ++
          allReachableStateLow(m, old = false, predicateSrc = m.pres)
        if (preservesOnly) {
          additionalInvs = additionalInvs.map(
            i => Implies(allVarsAndStateLow(m, m.formalArgs, old=true, predicateSrc = m.pres), i)())
        }
        val newInvs: Seq[Exp] = invs ++ additionalInvs
        While(cond, newInvs, body)(w.pos, w.info, w.errT)
    }
  }

  def isObligationVar(v: LocalVarDecl): Boolean = {
    val vi = v.info.getUniqueInfo[SIFInfo]
    vi match {
      case Some(info) => info.obligationVar
      case _ => false
    }
  }

  def obligationVars(m: Method): Seq[String] = {
    m.deepCollect[LocalVarDecl]({
      case d: LocalVarDecl if isObligationVar(d) => d
    }).map(v => v.name)
  }

  def createControlFlowVars(methodBody: Seqn): MethodControlFlowVars = {
    val gotos = methodBody.collect({case Goto(l) => l}).toSet
    val labels = methodBody.collect({case l@Label(n, _) if gotos.contains(n) => l}).toSet
    if (!Config.optimizeControlFlow) return new MethodControlFlowVars(true, true, true, true, labels)
    var hasRet, hasBreak, hasCont, hasExcept: Boolean = false
    methodBody.visit({
      case _: SIFReturnStmt => hasRet = true
      case _: SIFBreakStmt => hasBreak = true
      case _: SIFContinueStmt => hasCont = true
      case _: SIFRaiseStmt => hasExcept = true
      case _: SIFTryCatchStmt => hasExcept = true
    })
    if (labels.nonEmpty && (hasRet || hasBreak || hasCont || hasExcept))
      throw new IllegalArgumentException
    new MethodControlFlowVars(hasRet, hasBreak, hasCont, hasExcept, labels)
  }

  def incrementTime(p1: Exp, p2: Exp) : Seqn = {
    if (timing){
      val timeInc1 = If(p1, Seqn(Seq(LocalVarAssign(time.get, Add(time.get, IntLit(1)())())()), Seq())(), skip)()
      val timeInc2 = If(p2, Seqn(Seq(LocalVarAssign(translatePrime(time.get, p1, p2), translatePrime(Add(time.get, IntLit(1)())(), p1, p2))()), Seq())(), skip)()
      Seqn(Seq(timeInc1, timeInc2), Seq())()
    }else{
      skip
    }

  }

  private def terminationChannelsLowChecks(terminates: SIFTerminatesExp,
                                           ctx: TranslationContext): Seq[Exp] = {
    val condLowEventReasonTrafo = ErrTrafo({case _ =>
      SIFTerminationChannelCheckFailed(terminates, SIFTermCondLowEvent(terminates))}) +
      ReTrafo({case _ => SIFTermCondLowEvent(terminates)})
    val condLowReasonTrafo = ErrTrafo({case _ =>
      SIFTerminationChannelCheckFailed(terminates, SIFTermCondNotLow(terminates))}) +
      ReTrafo({case _ => SIFTermCondNotLow(terminates)})
    val pos = terminates.pos
    val info = terminates.info
    Seq(
      // Note: cast here is not very elegant, maybe there's a better way to attach the error reason
      // to result of translateSIFAss
      translateSIFAss(Implies(Not(terminates.cond)(pos, info, condLowEventReasonTrafo),
        SIFLowEventExp()(pos, info, condLowEventReasonTrafo))(pos, info, condLowEventReasonTrafo), ctx)
        .asInstanceOf[Implies].copy()(pos, info, condLowEventReasonTrafo),
      translateSIFAss(SIFLowExp(terminates.cond)(pos, info, condLowReasonTrafo), ctx)
        .asInstanceOf[Implies].copy()(pos, info, condLowReasonTrafo)
    )
  }

  /** Translate a predicate into MPP. Creates two copies of the predicate: one version for first execution,
    * one for the second. The predicates only contain the unary expressions of the original predicate.
    * Generates a function containing all the relational expressions in the predicates body.
    * @param pred The predicate to translate.
    * @return List of the new predicates, plus the low-function.
    */
  def translatePredicate(pred: Predicate): (Seq[Predicate], Seq[Option[Function]]) = {
    val unaryBody: Option[Exp] = translateToUnary(pred.body)

    val newPred = pred.copy(body = unaryBody)(pred.pos, pred.info, pred.errT)

    var lowF: Option[Function] = None
    var allLowF: Option[Function] = None
    if (pred.body.isDefined) {
      val (allLowFName, formalArgs, duplicatedFormalArgs) = predAllLowFuncInfo(pred.name).get

      val access1 = PredicateAccess(formalArgs.map{a => a.localVar}, newPred.name)(pred.pos)
      val access2 = PredicateAccess(duplicatedFormalArgs.map{a => a.localVar}, newPred.name)(pred.pos)
      val fPres: Seq[Exp] = Seq(And(PredicateAccessPredicate(access1, WildcardPerm()())(),
        PredicateAccessPredicate(access2, WildcardPerm()())())())
      val lowFFormalArgs = pred.formalArgs ++ duplicatedFormalArgs
      val primedBefore = primedNames.clone()
      formalArgs.zip(duplicatedFormalArgs).foreach(t => primedNames.update(t._1.name, t._2.name))

      def unfoldingPredicates(body: Exp): Exp = {
        Unfolding(PredicateAccessPredicate(access1, WildcardPerm()())(),
          Unfolding(PredicateAccessPredicate(access2, WildcardPerm()())(),
            body)())()
      }
      if (relationalPredicates.contains(pred)) {
        val (lowFName, _, _) = predLowFuncInfo(pred.name).get
        val fBody: Exp = unfoldingPredicates(translatePredLowFuncBody(pred.body.get))
        lowF = Some(Function(lowFName, lowFFormalArgs, Bool, fPres, Seq(), Some(fBody))
        (pred.pos, pred.info, pred.errT))
      }

      val allLowBody: Exp = unfoldingPredicates(translatePredAllLowFuncBody(pred.body.get))
      allLowF = Some(Function(allLowFName, lowFFormalArgs, Bool, fPres, Seq(), Some(allLowBody))
        (pred.pos, pred.info, pred.errT))

      primedNames.clear()
      primedNames ++= primedBefore
    }

    predLowFuncs.update(pred.name, lowF)
    predAllLowFuncs.update(pred.name, allLowF)
    if (Config.generateAllLowFuncs)
      (Seq(newPred), Seq(lowF, allLowF))
    else
      (Seq(newPred), Seq(lowF, None))
  }

  private def bypassPreamble(p1: Exp, p2: Exp, ctrlVars: MethodControlFlowVars,
                             bypass1r: LocalVar, bypass2r: LocalVar): Seq[Stmt] = {
    Seq(LocalVarAssign(bypass1r,
      Not(ctrlVars.activeExecNormal(Some(p1)))())(),
      LocalVarAssign(bypass2r, Not(ctrlVars.activeExecPrime(Some(p2)))())())
  }

  /** Translate a while statement into MPP.
    */
  private def translateWhileStmt(w: While, ctx: TranslationContext): Seqn = {
    val p1 = ctx.p1; val p2 = ctx.p2; val ctrlVars = ctx.ctrlVars

    // check if we need to do a reconstruction of this loop (iff it has ret/break/except stmt or we don't optimize)
    val recNeeded: Boolean = {
      var rn = !Config.optimizeControlFlow
    w.body.visit({
      case _: SIFReturnStmt => rn = true
      case _: SIFBreakStmt => rn = true
      case _: SIFRaiseStmt => rn = true
      case _: SIFTryCatchStmt => rn = true
    })
    rn
    }

    var newVarDecls = Seq[LocalVarDecl]()
    //var targetValRefs = Seq[LocalVar]()
    var targetValAssigns = Seq[Stmt]()
    var targetValEqualities1 = Set[Exp]()
    var targetValEqualities2 = Set[Exp]()

    val (bypass1d, bypass1r) = getNewBool("bypass1")
    val (bypass2d, bypass2r) = getNewBool("bypass2")
    newVarDecls ++= Seq(bypass1d, bypass2d)
    var stmts: Seq[Stmt] = bypassPreamble(p1, p2, ctrlVars, bypass1r, bypass2r)

    def targetCollectF: PartialFunction[Node, Seq[LocalVar]] = {
      case LocalVarAssign(lhs, _) => Seq(lhs)
      case MethodCall(_, _, ts) => ts
      case NewStmt(t, _) => Seq(t)
      case SIFReturnStmt(_, _) => Seq(ctrlVars.ret1r.get)
      case SIFRaiseStmt(_) => Seq(ctrlVars.except1r.get)
      case SIFTryCatchStmt(body, handlers, elseBlock, finallyBlock) =>
        (body.deepCollect(targetCollectF).distinct.flatten ++
        handlers.map(h => h.body.deepCollect(targetCollectF).flatten).distinct.flatten ++ (elseBlock match {
          case Some(eb) => eb.deepCollect(targetCollectF).distinct.flatten
          case None => Seq()
        }) ++ (finallyBlock match {
          case Some(fb) => fb.deepCollect(targetCollectF).distinct.flatten
          case None => Seq()
        })).distinct
    }

    // continue and break control variables will be assigned even if there is no continue in this loop -> add to targets
    val targets = w.deepCollect(targetCollectF).flatten.distinct ++ (if (ctrlVars.cont1r.isDefined)
      Seq(ctrlVars.cont1r.get, ctrlVars.cont2r.get) else Seq()) ++ (if (ctrlVars.break1r.isDefined)
      Seq(ctrlVars.break1r.get, ctrlVars.break2r.get) else Seq())

    var tmpAssigns1 = Seq[LocalVarAssign]()
    var tmpAssigns2 = Seq[LocalVarAssign]()
    for (t <- targets) {
      // make sure the variable is defined outside the loop
      if (primedNames.contains(t.name)){
        val (tmp1d, tmp1r) = getNewVar("tmp1", t.typ)
        val (tmp2d, tmp2r) = getNewVar("tmp2", t.typ)
        newVarDecls ++= Seq(tmp1d, tmp2d)
        //targetValRefs ++= Seq(tmp1r, tmp2r)
        tmpAssigns1 :+= LocalVarAssign(tmp1r, t)()
        tmpAssigns2 :+= LocalVarAssign(tmp2r, translatePrime(t, p1, p2))()
        val eq1 = EqCmp(tmp1r, t)()
        val eq2 = EqCmp(tmp2r, translatePrime(t, p1, p2))()
        targetValEqualities1 ++= Seq(eq1)
        targetValEqualities2 ++= Seq(eq2)
      }
    }
    if (tmpAssigns1.nonEmpty) targetValAssigns :+= If(bypass1r, Seqn(tmpAssigns1, Seq())(), skip)()
    if (tmpAssigns2.nonEmpty) targetValAssigns :+= If(bypass2r, Seqn(tmpAssigns2, Seq())(), skip)()

    /*if (timing){
      val (tmp1d, tmp1r) = getNewVar("tmp1", Int)
      val (tmp2d, tmp2r) = getNewVar("tmp2", Int)
      newVarDecls ++= Seq(tmp1d, tmp2d)
      val assign1 = LocalVarAssign(tmp1r, time.get)()
      val assign2 = LocalVarAssign(tmp2r, translatePrime(time.get, p1, p2))()
      targetValAssigns ++= Seq(assign1, assign2)
      val eq1 = EqCmp(tmp1r, time.get)()
      val eq2 = EqCmp(tmp2r, translatePrime(time.get, p1, p2))()
      targetValEqualities1 ++= Seq(eq1)
      targetValEqualities2 ++= Seq(eq2)
    }*/
    stmts ++= targetValAssigns

    // tmp assigns for all ctrlVars
    var ctrlVarToOldMap: Map[LocalVar, LocalVar] = Map()
    if (recNeeded) {
      var ctrlFlowTmpAssigns = Seq[Stmt]()
      for (v <- ctrlVars.declarations().map(d => d.localVar)) {
        val (tmp1d, tmp1r) = getNewBool("old" + v.name)
        ctrlVarToOldMap += (v -> tmp1r)
        newVarDecls :+= tmp1d
        stmts :+= LocalVarAssign(tmp1r, v)()
        ctrlFlowTmpAssigns :+= LocalVarAssign(v, tmp1r)()
      }
    }

    val newCond = Or(And(And(ctrlVars.activeExecNoContNormal(Some(p1)), Not(bypass1r)())(), w.cond)(),
      And(And(ctrlVars.activeExecNoContPrime(Some(p2)), Not(bypass2r)())(), translatePrime(w.cond, p1, p2))())()
    var bodyPreamble: Seq[Stmt] = Seq()
    if (ctrlVars.cont1r.isDefined) bodyPreamble = bodyPreamble :+
      LocalVarAssign(ctrlVars.cont1r.get, FalseLit()())() :+
      LocalVarAssign(ctrlVars.cont2r.get, FalseLit()())()
    val (p1d, p1r) = getNewBool("p1")
    val (p2d, p2r) = getNewBool("p2")
    newVarDecls ++= Seq(p1d, p2d)
    val p1Assign = LocalVarAssign(p1r, And(ctrlVars.activeExecNormal(Some(p1)), w.cond)())()
    val p2Assign = LocalVarAssign(p2r, And(ctrlVars.activeExecPrime(Some(p2)), translatePrime(w.cond, p1, p2))())()
    bodyPreamble ++= Seq(p1Assign, p2Assign)

    var newStdInvs = w.invs
    // check if there is an InhaleExhaleExp in invariants
    if (w.invs.exists(inv => inv.contains[InhaleExhaleExp])) {
      val (idle1d, idle1r) = getNewBool("idle1")
      val (idle2d, idle2r) = getNewBool("idle2")
      primedNames.update(idle1r.name, idle2r.name)
      newVarDecls ++= Seq(idle1d, idle2d)
      // assign false before the loop
      stmts ++= Seq(LocalVarAssign(idle1r, FalseLit()())(),
        LocalVarAssign(idle2r, FalseLit()())())
      // assign inside loop body that the execution is idling
      val idle1Assign = LocalVarAssign(idle1r,
        And(ctrlVars.activeExecNormal(Some(p1)), Not(w.cond)())())()
      val idle2Assign = LocalVarAssign(idle2r,
        And(ctrlVars.activeExecPrime(Some(p2)), Not(translatePrime(w.cond, p1, p2))())())()
      bodyPreamble ++= Seq(idle1Assign, idle2Assign)
      // make all exhales of InhaleExhales dependent on not idling
      newStdInvs = newStdInvs.map(inv => inv.transform{
        case ie@InhaleExhaleExp(in, ex) => InhaleExhaleExp(in,
          Implies(Not(idle1r)(), ex)())(ie.pos, ie.info, ie.errT)
      })
    }

    // --- Terminates ---
    var terminates: Option[SIFTerminatesExp] = None
    w.invs.foreach(inv => inv.visit{
      case t: SIFTerminatesExp => terminates = Some(t)
    })
    if (terminates.isDefined) {
      stmts ++= terminationChannelsLowChecks(terminates.get, ctx)
        .map(tc => Assert(tc)(tc.pos, tc.info, tc.errT))
      val (cond1d, cond1r) = getNewBool("cond")
      val (cond2d, cond2r) = getNewBool("cond")
      primedNames.update(cond1r.name, cond2r.name)
      newVarDecls ++= Seq(cond1d, cond2d)
      stmts ++= Seq(If(p1, Seqn(Seq(LocalVarAssign(cond1r, terminates.get.cond)()), Seq())(), skip)(),
        If(p2, Seqn(Seq(LocalVarAssign(cond2r, translatePrime(terminates.get.cond, p1, p2))()), Seq())(), skip)())
      newStdInvs :+= Implies(Not(cond1r)(), w.cond)(
        terminates.get.pos, terminates.get.info, ErrTrafo({
          case _ => SIFTerminationChannelCheckFailed(terminates.get, SIFTermCondNotTight(terminates.get))
        }))
    }

    val invCtx = ctx.copy(
      p1 = And(p1, Not(bypass1r)())(),
      p2 = And(p2, Not(bypass2r)())()
    )
    /*
    val invCtx = ctx.copy(
      p1 = ctrlVars.activeExecNoContNormal(Some(p1)),
      p2 = ctrlVars.activeExecNoContPrime(Some(p2))
    )
     */
    newStdInvs = simplifyConditions(newStdInvs.map(e => translateSIFAss(e, invCtx, invCtx)))
    val newInvs: Seq[Exp] = newStdInvs ++
      targetValEqualities1.map(e => Implies(bypass1r, e)()) ++
      targetValEqualities2.map(e => Implies(bypass2r, e)())

    val bodyRes = translateStatement(w.body, ctx.copy(p1 = p1r, p2 = p2r))
    /*val bodyPostamble = Seq(
      Inhale(Or(Not(p1)(), ctrlVars.activeExecNoContNormal(None))())(),
      Inhale(Or(Not(p2)(), ctrlVars.activeExecNoContPrime(None))())()
    )*/
    stmts :+= While(newCond, newInvs, Seqn(bodyPreamble ++ Seq(bodyRes), Seq())())()

    // loop reconstruction
    if (recNeeded) {
      val recCond1 = And(Not(bypass1r)(), Seq(ctrlVars.ret1r, ctrlVars.break1r, ctrlVars.except1r)
        .collect({ case Some(x) => x })
        .reduceRight[Exp]((x, y) => Or(x, y)())
      )()
      val recCond2 = And(Not(bypass2r)(), Seq(ctrlVars.ret2r, ctrlVars.break2r, ctrlVars.except2r)
        .collect({ case Some(x) => x })
        .reduceRight[Exp]((x, y) => Or(x, y)()))()
      val recCond = Or(recCond1, recCond2)()
      val ctrlVarAssigns: Seq[Stmt] = ctrlVars.declarations()
        .map(d => d.localVar)
        .map(v => LocalVarAssign(v, ctrlVarToOldMap(v))())
      val recInhales: Seq[Stmt] = Seq() :+ //newStdInvs.map(i => Inhale(i)()) :+
        Inhale(Implies(ctrlVars.activeExecNoContNormal(Some(p1)), w.cond)())() :+
        Inhale(Implies(ctrlVars.activeExecNoContNormal(Some(p2)), translatePrime(w.cond, p1, p2))())()
      val recKillInhales: Seq[Stmt] = Seq(
        Inhale(Or(Not(p1r)(), Not(ctrlVars.activeExecNoContNormal(None))())())(),
        Inhale(Or(Not(p2r)(), Not(ctrlVars.activeExecNoContPrime(None))())())()
      )
      val recThn = Seqn(
        (ctrlVarAssigns ++ recInhales ++ bodyPreamble ++ Seq(bodyRes) ++ recKillInhales),
        Seq())()
      stmts :+= If(recCond, recThn, skip)(info=SimpleInfo(Seq("Loop Reconstruction.\n  ")))
    }
    if (Seq(ctrlVars.break1r, ctrlVars.cont1r).collect({case Some(x) => x}).nonEmpty) {
      stmts ++= Seq(
        If(Not(bypass1r)(), Seqn(Seq(ctrlVars.break1r, ctrlVars.cont1r)
          .collect({ case Some(x) => x })
          .map(v => LocalVarAssign(v, FalseLit()())()),
          Seq())(), skip)(),
        If(Not(bypass2r)(), Seqn(Seq(ctrlVars.break2r, ctrlVars.cont2r)
          .collect({ case Some(x) => x })
          .map(v => LocalVarAssign(v, FalseLit()())()),
          Seq())(), skip)()
      )
    }
    Seqn(stmts, newVarDecls)()
  }

  /** Translate a try/catch block into MPP.
    */
  private def translateTryCatchStmt(tryStmt: SIFTryCatchStmt, ctx: TranslationContext): Seqn = {
    val p1 = ctx.p1; val p2 = ctx.p2; val ctrlVars = ctx.ctrlVars
    var stmts: Seq[Stmt] = Seq()
    var newVarDecls: Seq[LocalVarDecl] = Seq()
    val hasFinally: Boolean = tryStmt.finallyBlock.isDefined
    // bypass preamble
    val (bypass1d, bypass1r) = getNewBool("bypass1")
    val (bypass2d, bypass2r) = getNewBool("bypass2")
    newVarDecls ++= Seq(bypass1d, bypass2d)
    val bypassAssigns: Seq[Stmt] = bypassPreamble(p1, p2, ctrlVars, bypass1r, bypass2r)
    stmts ++= bypassAssigns
    // assigning old values of ret and except flags
    def oldAssign(ctrl: Option[LocalVar], name: String): Option[LocalVar] = {
      if (ctrl.isEmpty) return None
      val (decl, v) = getNewBool(name)
      newVarDecls :+= decl
      stmts :+= LocalVarAssign(v, ctrl.get)()
      Some(v)
    }
    var oldret1r, oldret2r, oldbreak1r, oldbreak2r, oldcont1r, oldcont2r,
      oldexcept1r, oldexcept2r: Option[LocalVar] = None
    if (hasFinally) {
      oldret1r    = oldAssign(ctrlVars.ret1r,    name = "oldret1")
      oldret2r    = oldAssign(ctrlVars.ret2r,    name = "oldret2")
      oldbreak1r  = oldAssign(ctrlVars.break1r,  name = "oldbreak1")
      oldbreak2r  = oldAssign(ctrlVars.break2r,  name = "oldbreak2")
      oldcont1r   = oldAssign(ctrlVars.cont1r,   name = "oldcont1")
      oldcont2r   = oldAssign(ctrlVars.cont2r,   name = "oldcont2")
      oldexcept1r = oldAssign(ctrlVars.except1r, name = "oldexcept1")
      oldexcept2r = oldAssign(ctrlVars.except2r, name = "oldexcept2")
    }
    // translate try body
    stmts :+= translateStatement(tryStmt.body, ctx)
    // create variable 'thisexcept', to express that we had an exception in this tryblock
    val (thisexcept1d, thisexcept1r) = getNewBool("thisexcept1")
    val (thisexcept2d, thisexcept2r) = getNewBool("thisexcept2")
    newVarDecls ++= Seq(thisexcept1d, thisexcept2d)
    stmts :+= LocalVarAssign(thisexcept1r, And(ctrlVars.except1r.get, Not(bypass1r)())())()
    stmts :+= LocalVarAssign(thisexcept2r, And(ctrlVars.except2r.get, Not(bypass2r)())())()
    // translate the exception handlers
    for (handler <- tryStmt.catchBlocks) {
      val (p1d, p1r) = getNewBool("p1")
      val (p2d, p2r) = getNewBool("p2")
      newVarDecls ++= Seq(p1d, p2d)
      stmts = stmts :+
        LocalVarAssign(p1r, And(p1, And(thisexcept1r, translateNormal(handler.exception, p1, p2))())())() :+
        LocalVarAssign(p2r, And(p2, And(thisexcept2r, translatePrime(handler.exception, p1, p2))())())() :+
        If(p1r, Seqn(Seq(LocalVarAssign(ctrlVars.except1r.get, FalseLit()())()), Seq())(), skip)() :+
        If(p2r, Seqn(Seq(LocalVarAssign(ctrlVars.except2r.get, FalseLit()())()), Seq())(), skip)()
      stmts :+= translateStatement(handler.body, TranslationContext(p1r, p2r, ctrlVars, ctx.currentMethod))
      // assign null to error variable if exception was caught
      stmts :+= translateStatement(LocalVarAssign(handler.errVar, NullLit()())(), ctx)
    }
    // translate the else block
    if (tryStmt.elseBlock.isDefined) {
      val (p1d2, p1r2) = getNewBool("p1")
      val (p2d2, p2r2) = getNewBool("p2")
      newVarDecls ++= Seq(p1d2, p2d2)
      stmts :+= LocalVarAssign(p1r2, And(p1, Not(thisexcept1r)())())()
      stmts :+= LocalVarAssign(p2r2, And(p2, Not(thisexcept2r)())())()
      stmts :+= translateStatement(tryStmt.elseBlock.get, TranslationContext(p1r2, p2r2, ctrlVars, ctx.currentMethod))
    }
    // translate the finally block
    if (hasFinally) {
      def tmpAssigns(tuples: (LocalVar, Option[LocalVar], Option[LocalVar])*): Seq[Stmt] = {
        tuples
          .filter(tuple => tuple._2.isDefined)
          .flatMap{
            case (tmp: LocalVar, ctrl: Option[LocalVar], old: Option[LocalVar]) =>
              Seq(LocalVarAssign(tmp, ctrl.get)(),
                LocalVarAssign(ctrl.get, old.get)())
          }
      }
      def tmpReAssigns(tuples: (LocalVar, Option[LocalVar], Option[Seq[Option[LocalVar]]])*): Seq[Stmt] = {
        tuples
          .filter(tuple => tuple._2.isDefined)
          .flatMap{
            case (tmp: LocalVar, ctrl: Option[LocalVar], None) =>
              Seq(LocalVarAssign(ctrl.get, Or(ctrl.get, tmp)())())
            case (tmp: LocalVar, ctrl: Option[LocalVar], Some(unless)) =>
              val negatedUnless = unless.map{
                case Some(v) => Some(Not(v)())
                case None => None
              }
              Seq(LocalVarAssign(ctrl.get, Or(ctrl.get, And(tmp, _conjoinOptions(negatedUnless))())())())
          }
      }

      // store ret and except in tmp variables
      val (tmpret1d, tmpret1r) = getNewBool("tmp_ret1")
      val (tmpret2d, tmpret2r) = getNewBool("tmp_ret2")
      val (tmpbreak1d, tmpbreak1r) = getNewBool("tmp_break1")
      val (tmpbreak2d, tmpbreak2r) = getNewBool("tmp_break2")
      val (tmpcont1d, tmpcont1r) = getNewBool("tmp_cont1")
      val (tmpcont2d, tmpcont2r) = getNewBool("tmp_cont2")
      val (tmpexcept1d, tmpexcept1r) = getNewBool("tmp_except1")
      val (tmpexcept2d, tmpexcept2r) = getNewBool("tmp_except2")
      newVarDecls ++= Seq(tmpret1d, tmpret2d, tmpbreak1d, tmpbreak2d, tmpcont1d, tmpcont2d,
        tmpexcept1d, tmpexcept2d)
      val tmpAssigns1: Seq[Stmt] = tmpAssigns(
        (tmpret1r, ctrlVars.ret1r, oldret1r),
        (tmpbreak1r, ctrlVars.break1r, oldbreak1r),
        (tmpcont1r, ctrlVars.cont1r, oldcont1r),
        (tmpexcept1r, ctrlVars.except1r, oldexcept1r)
      )
      val tmpAssigns2: Seq[Stmt] = tmpAssigns(
        (tmpret2r, ctrlVars.ret2r, oldret2r),
        (tmpbreak2r, ctrlVars.break2r, oldbreak2r),
        (tmpcont2r, ctrlVars.cont2r, oldcont2r),
        (tmpexcept2r, ctrlVars.except2r, oldexcept2r)
      )
      stmts :+= If(p1, Seqn(tmpAssigns1, Seq())(), skip)()
      stmts :+= If(p2, Seqn(tmpAssigns2, Seq())(), skip)()
      stmts :+= translateStatement(tryStmt.finallyBlock.get, ctx)
      val tmpReAssigns1 = tmpReAssigns(
        (tmpexcept1r, ctrlVars.except1r, Some(Seq(ctrlVars.ret1r, ctrlVars.break1r))),
        (tmpret1r, ctrlVars.ret1r, None),
        (tmpbreak1r, ctrlVars.break1r, None),
        (tmpcont1r, ctrlVars.cont1r, None)
      )
      val tmpReAssigns2 = tmpReAssigns(
        (tmpexcept2r, ctrlVars.except2r, Some(Seq(ctrlVars.ret2r, ctrlVars.break2r))),
        (tmpret2r, ctrlVars.ret2r, None),
        (tmpbreak2r, ctrlVars.break2r, None),
        (tmpcont2r, ctrlVars.cont2r, None)
      )
      stmts :+= If(p1, Seqn(tmpReAssigns1, Seq())(), skip)()
      stmts :+= If(p2, Seqn(tmpReAssigns2, Seq())(), skip)()
    }
    Seqn(stmts, newVarDecls)(info = SimpleInfo(Seq("Try/catch block\n  ")))
  }

  def translateWandPackage(p: Package, ctx: TranslationContext): Stmt = {
    val Package(w@MagicWand(left, right), proofScript) = p
    // Package(
    //   MagicWand(
    //     translateSIFAss(left, ctx), 
    //     translateSIFAss(right, ctx)
    //   )(w.pos, w.info, w.errT), 
    //   Seqn(Seq(translateStatement(proofScript, ctx)), Seq())()
    // )(p.pos, p.info, p.errT)
    val p1 = ctx.p1
    val p2 = ctx.p2
    lazy val act1: Exp = ctx.ctrlVars.activeExecNormal(Some(p1))
    lazy val act2: Exp = ctx.ctrlVars.activeExecPrime(Some(p2))

    val leftNormal = translateNormal(left, p1, p2)
    val rightNormal = translateNormal(right, p1, p2)
    val wandNormal = MagicWand(leftNormal, rightNormal)(w.pos, w.info, w.errT)
    val proofScriptNormal = proofScript.transform{
      case e: Exp => translateNormal(e, act1, act2)
    }
    val packageNormal = Package(wandNormal, proofScriptNormal)(p.pos, p.info, p.errT)
    val ifNormal = If(act1, Seqn(Seq(packageNormal), Seq())(), skip)()

    val leftPrime = translatePrime(left, p1, p2)
    val rightPrime = translatePrime(right, p1, p2)
    val wandPrime = MagicWand(leftPrime, rightPrime)(w.pos, w.info, w.errT)
    val proofScriptPrime = proofScript.transform{
      case e: Exp => translatePrime(e, act1, act2)
    }
    val packagePrime = Package(wandPrime, proofScriptPrime)(p.pos, p.info, p.errT)
    val ifPrime = If(act2, Seqn(Seq(packagePrime), Seq())(), skip)()

    Seqn(Seq(ifNormal, ifPrime), Seq())()
  }

  def translateWandApply(a: Apply, ctx: TranslationContext): Stmt = {
    val Apply(w@MagicWand(left, right)) = a
    // Apply(
    //   MagicWand(
    //     translateSIFAss(left, ctx), 
    //     translateSIFAss(right, ctx)
    //   )(w.pos, w.info, w.errT), 
    // )(a.pos, a.info, a.errT)

    val p1 = ctx.p1
    val p2 = ctx.p2
    lazy val act1: Exp = ctx.ctrlVars.activeExecNormal(Some(p1))
    lazy val act2: Exp = ctx.ctrlVars.activeExecPrime(Some(p2))

    val leftNormal = translateNormal(left, p1, p2)
    val rightNormal = translateNormal(right, p1, p2)
    val wandNormal = MagicWand(leftNormal, rightNormal)(w.pos, w.info, w.errT)
    val applyNormal = Apply(wandNormal)(a.pos, a.info, a.errT)
    val ifNormal = If(act1, Seqn(Seq(applyNormal), Seq())(), skip)()

    val leftPrime = translatePrime(left, p1, p2)
    val rightPrime = translatePrime(right, p1, p2)
    val wandPrime = MagicWand(leftPrime, rightPrime)(w.pos, w.info, w.errT)
    val applyPrime = Apply(wandPrime)(a.pos, a.info, a.errT)
    val ifPrime = If(act2, Seqn(Seq(applyPrime), Seq())(), skip)()

    Seqn(Seq(ifNormal, ifPrime), Seq())()
  }

  def translateStatement(s: Stmt, ctx: TranslationContext) : Stmt = {
    val p1 = ctx.p1
    val p2 = ctx.p2
    val ctrlVars = ctx.ctrlVars
    lazy val act1: Exp = ctx.ctrlVars.activeExecNormal(Some(p1))
    lazy val act2: Exp = ctx.ctrlVars.activeExecPrime(Some(p2))

    def executeConditionally(ift1: Seqn, ift2: Seqn): Stmt = {
      val a1 = If(act1, ift1, skip)()
      val a2 = If(act2, ift2, skip)()
      Seqn(Seq(a1, a2, incrementTime(p1, p2)), Seq())()
    }
    def translateAssignment(to1: LocalVar, v1: Exp, to2: LocalVar, v2: Exp, orig: Stmt) : Stmt = {
      executeConditionally(
        Seqn(Seq(LocalVarAssign(to1, v1)(orig.pos, orig.info, orig.errT)), Seq())(),
        Seqn(Seq(LocalVarAssign(to2, v2)(orig.pos, orig.info, orig.errT)), Seq())()
      )
    }

    /** Return true if the statement can be bunched together with others, without doing the interleaving of the
      * two executions, thus saving on the number of if-statements generated.
      */
    def isCompressible(s: Stmt): Boolean = {
      s match {
        case _: LocalVarAssign => true
        case Inhale(e) => isUnary(e)
        case Exhale(e) => isUnary(e)
        case _: SIFReturnStmt => true
        case _: SIFBreakStmt => true
        case _: SIFContinueStmt => true
        case _: Goto => false
        case _: Label => false
        case _ => false
      }
    }

    /** Do the translation of a statement without wrapping it in an if statement. Just returns the two versions in a
      * tuple, to allow putting multiple statements in an if block. Requires [[isCompressible(s)]].
      */
    def translateStmtPartial(s: Stmt): (Stmt, Stmt) = {
      assert(isCompressible(s))
      s match {
        case l@LocalVarAssign(lhs, rhs) => (LocalVarAssign(translateNormal(lhs, p1, p2),
          translateNormal(rhs, p1, p2))(l.pos, l.info, l.errT),
          LocalVarAssign(translatePrime(lhs, p1, p2), translatePrime(rhs, p1, p2))(l.pos, l.info, l.errT))
        case a@FieldAssign(lhs, rhs) => (a, FieldAssign(translatePrime(lhs, p1, p2),
          translatePrime(rhs, p1, p2))(a.pos, a.info, a.errT))
        case i@Inhale(e) => (Inhale(translateNormal(e, p1, p2))(i.pos, i.info, i.errT),
          Inhale(translatePrime(e, p1, p2))(i.pos, i.info, i.errT))
        case ex@Exhale(e) => (Exhale(translateNormal(e, p1, p2))(ex.pos, ex.info, ex.errT),
          Exhale(translatePrime(e, p1, p2))(ex.pos, ex.info, ex.errT))
        case b: SIFBreakStmt => {
          // TODO
          (LocalVarAssign(ctrlVars.break1r.get, TrueLit()())(b.pos, b.info, b.errT),
            LocalVarAssign(ctrlVars.break2r.get, TrueLit()())(b.pos, b.info, b.errT))
        }
        case c: SIFContinueStmt => (LocalVarAssign(ctrlVars.cont1r.get, TrueLit()())(c.pos, c.info, c.errT),
          LocalVarAssign(ctrlVars.cont2r.get, TrueLit()())(c.pos, c.info, c.errT))
        case r@SIFReturnStmt(e, resVar) =>
          {
            // TODO
            val assign1 = resVar match {
              case Some(rv) => Seq(LocalVarAssign(translateNormal(rv, p1, p2),
                translateNormal(e.get, p1, p2))(r.pos, r.info, r.errT))
              case None => Seq()
            }
            val assign2 = resVar match {
              case Some(rv) => Seq(LocalVarAssign(translatePrime(rv, p1, p2),
                translatePrime(e.get, p1, p2))(r.pos, r.info, r.errT))
              case None => Seq()
            }
            (Seqn(assign1 :+ LocalVarAssign(ctrlVars.ret1r.get, TrueLit()())(), Seq())(),
              Seqn(assign2 :+ LocalVarAssign(ctrlVars.ret2r.get, TrueLit()())(), Seq())())
          }

        case _ => throw new IllegalArgumentException(s"The statement $s can't be translated partially")
      }
    }

    def optimizeSequential(s: Seqn): Seq[Stmt] = {
      def sequenceSplit(in: Seq[Stmt]): (Seq[Stmt], Seq[Stmt]) = {
        // ensure that we make a split after return, break, continue, raise, because the ctrlVars will have changed
        var stop: Boolean = false
        def keepGoing(stmt: Stmt): Boolean = {
          val oldStop = stop
          stmt match {
            case _: SIFReturnStmt   => stop = true
            case _: SIFBreakStmt    => stop = true
            case _: SIFContinueStmt => stop = true
            case _: SIFRaiseStmt    => stop = true
            case _ =>
          }
          !oldStop && isCompressible(stmt)
        }
        in.span(stmt => keepGoing(stmt))
      }

      var newStmts = Seq[Stmt]()
      var (comp, rest) = sequenceSplit(s.ss)
//      println("optimizing compressible statements:")
      while (comp.nonEmpty || rest.nonEmpty) {
//        println(s"split into comp: $comp and rest: $rest")
        // collect all compressible statements we have until here
        if (comp.nonEmpty) {
          val (fstExComp, secExComp): (Seq[Stmt], Seq[Stmt]) = comp.map(stmt => translateStmtPartial(stmt)).unzip
          newStmts :+= executeConditionally(Seqn(fstExComp, Seq())(), Seqn(secExComp, Seq())())
        }
        // translate all non-compressible statements
        var split = rest.span(stmt => !isCompressible(stmt))
        val nonComp = split._1
        rest = split._2
//        println(s"split into non-comp: $nonComp and rest: $rest")
        nonComp.foreach(stmt => newStmts :+= translateStatement(stmt, ctx))
        // start anew
        split = sequenceSplit(rest)
        comp = split._1
        rest = split._2
      }
      newStmts
    }

    s match {
      case l@LocalVarAssign(lhs, rhs)  => translateAssignment(translateNormal(lhs, p1, p2),
        translateNormal(rhs, p1, p2), translatePrime(lhs, p1, p2), translatePrime(rhs, p1, p2), l)
      case a@FieldAssign(lhs, rhs)  => executeConditionally(Seqn(Seq(a), Seq())(),
          Seqn(Seq(FieldAssign(translatePrime(lhs, p1, p2),
            translatePrime(rhs, p1, p2))(a.pos, a.info, a.errT)), Seq())())
      case NewStmt(lhs, fields) => {
        val allFields = fields ++ fields.map{f => newFields.find(f2 => f2.name == primedNames(f.name)).get}
        val (tmpd, tmpr) = getNewVar("tmp", Ref)
        val newNew = NewStmt(tmpr, allFields)()
        /*val allFieldAssigns = allFields.map { f =>
          val (hd, hr) = getNewVar("havoc", f.typ)
          val fieldAcc = FieldAccess(tmpr, f)()
          Seqn(Seq(FieldAssign(fieldAcc, hr)()), Seq(hd))()
        }*/
        val assign1 = If(act1, Seqn(Seq(LocalVarAssign(lhs, tmpr)()), Seq())(), skip)()
        val assign2 = If(act2, Seqn(Seq(LocalVarAssign(translatePrime(lhs, p1, p2), tmpr)()),
            Seq())(), skip)()
        Seqn(Seq(newNew) ++  /*allFieldAssigns ++*/ Seq(assign1, assign2, incrementTime(p1, p2)), Seq(tmpd))()
      }
      case i@If(cond, thn, els) => {
        val (p1d, p1r) = getNewBool("p1")
        val (p2d, p2r) = getNewBool("p2")
        val (p3d, p3r) = getNewBool("p3")
        val (p4d, p4r) = getNewBool("p4")

        val p1Assign = LocalVarAssign(p1r, And(act1, cond)())(i.pos)
        val p2Assign = LocalVarAssign(p2r, And(act2, translatePrime(cond, p1, p2))())(i.pos)
        val p3Assign = LocalVarAssign(p3r, And(act1, Not(cond)())())(i.pos)
        val p4Assign = LocalVarAssign(p4r, And(act2, Not(translatePrime(cond, p1, p2))())())(i.pos)

        val thnRes = translateStatement(thn, TranslationContext(p1r, p2r, ctrlVars, ctx.currentMethod))
        val elsRes = translateStatement(els, TranslationContext(p3r, p4r, ctrlVars, ctx.currentMethod))
        Seqn(Seq(p1Assign, p2Assign, p3Assign, p4Assign, incrementTime(p1, p2), thnRes, elsRes), Seq(p1d, p2d, p3d, p4d))()
      }
      case w: While => translateWhileStmt(w, ctx)
      case mc@MethodCall(name, args, targets) => {
        var argDecls = Seq[LocalVarDecl]()
        var newArgs = Seq[Exp](act1, act2)
        var argAssigns1 = Seq[LocalVarAssign]()
        var argAssigns2 = Seq[LocalVarAssign]()

        if (timing){
          newArgs ++= Seq(time.get, translatePrime(time.get, p1, p2))
        }

        for (a <- args){
          val (tmp1d, tmp1r) = getNewVar("tmp1", a.typ)
          val (tmp2d, tmp2r) = getNewVar("tmp2", a.typ)
          argDecls ++= Seq(tmp1d, tmp2d)
          newArgs ++= Seq(tmp1r, tmp2r)
          argAssigns1 :+= LocalVarAssign(tmp1r, a)()
          argAssigns2 :+= LocalVarAssign(tmp2r, translatePrime(a, p1, p2))()
        }
        val argAssignsConditional: Seq[Stmt] = Seq(
          If(act1, Seqn(argAssigns1, Seq())(), skip)(),
          If(act2, Seqn(argAssigns2, Seq())(), skip)()
        )

        var targetDecls = Seq[LocalVarDecl]()
        var newTargets = Seq[LocalVar]()
        var targetAssigns1 = Seq[LocalVarAssign]()
        var targetAssigns2 = Seq[LocalVarAssign]()

        if (timing){
          newTargets ++= Seq(time.get, translatePrime(time.get, p1, p2))
        }

        for (t <- targets){
          val (tmp1d, tmp1r) = getNewVar("tmp1", t.typ)
          val (tmp2d, tmp2r) = getNewVar("tmp2", t.typ)
          targetDecls ++= Seq(tmp1d, tmp2d)
          newTargets ++= Seq(tmp1r, tmp2r)
          targetAssigns1 :+= LocalVarAssign(t, tmp1r)()
          targetAssigns2 :+= LocalVarAssign(translatePrime(t, p1, p2), tmp2r)()
        }
        val targetAssignsConditional = if (targets.nonEmpty) Seq[Stmt](
          If(act1, Seqn(targetAssigns1, Seq())(), skip)(),
          If(act2, Seqn(targetAssigns2, Seq())(), skip)()
        ) else Seq()

        val call = MethodCall(name, newArgs, newTargets)(mc.pos, mc.info, mc.errT)
        If(Or(act1, act2)(),
          Seqn(argAssignsConditional ++ Seq(call) ++ targetAssignsConditional, argDecls ++ targetDecls)(),
          skip
        )(info = SimpleInfo(Seq(s"Method call: $name\n  ")))
      }
      case s: Seqn => {
        val seq = if (Config.optimizeSequential) flattenSeqn(s) else s
        var newDecls = Seq[Declaration]()
        for (d <- seq.scopedDecls.filter(d => d.isInstanceOf[LocalVarDecl])){
          val newName = getName(d.name)
          primedNames.update(d.name, newName)
          val newD = LocalVarDecl(newName, d.asInstanceOf[LocalVarDecl].typ)()
          newDecls ++= Seq(d, newD)
        }
        newDecls ++= seq.scopedDecls.filter(d => d.isInstanceOf[Label])
        val newStmts = if (Config.optimizeSequential) optimizeSequential(seq)
          else seq.ss.map{stmt => translateStatement(stmt, ctx)}
        Seqn(newStmts, newDecls)()
      }
      case a@Assert(e1) =>
        val newCtx = a.info.getUniqueInfo[SIFInfo] match {
          case Some(info) if info.continueUnaware => ctx.copy(p1 = ctrlVars.activeExecNoContNormal(Some(p1)),
            p2 = ctrlVars.activeExecNoContPrime(Some(p2)))
          case _ => ctx.copy(p1 = act1, p2 = act2)
        }
        Assert(translateSIFAss(e1, newCtx))(s.pos, errT= fwTs(s, s))
      case i@Inhale(FalseLit()) => i
      case Assume(e1) => Assume(translateSIFAss(e1, ctx.copy(p1 = act1, p2 = act2)))(s.pos, errT= fwTs(s, s))
      case Inhale(e1) => Inhale(translateSIFAss(e1, ctx.copy(p1 = act1, p2 = act2)))(s.pos, errT= fwTs(s, s))
      case Exhale(e1) => Exhale(translateSIFAss(e1, ctx.copy(p1 = act1, p2 = act2)))(s.pos, errT= fwTs(s, s))
      case d : LocalVarDeclStmt => d
      case u@Unfold(acc) =>
        val predicate2 = PredicateAccess(acc.loc.args.map(a => translatePrime(a, p1, p2)),
          acc.loc.predicateName)()
        val (lowFunc, lhs) = getPredicateLowFuncExp(acc.loc.predicateName, ctx)
        val assert = lowFunc match {
          case Some(f) =>
            val et = ErrTrafo({case _: AssertFailed => errors.UnfoldFailed(u, SIFUnfoldNotLow(u))})
            Assert(Implies(
              lhs,
              Implies(
                And(
                  PermGeCmp(CurrentPerm(acc.loc)(), FullPerm()())(),
                  PermGeCmp(CurrentPerm(predicate2)(), FullPerm()())()
                )(),
                FuncApp(f, acc.loc.args ++ acc.loc.args.map(a => translatePrime(a, p1, p2)))()
              )())()
            )(u.pos, u.info, errT = et)
          case None => skip
        }
        val if1 = If(act1, Seqn(Seq(u), Seq())(), skip)()
        val if2 = If(act2, Seqn(Seq(
          Unfold(PredicateAccessPredicate(predicate2, translatePrime(acc.perm, p1, p2))())(u.pos, u.info, u.errT)
        ), Seq())(), skip)()
        Seqn(Seq(assert, if1, if2), Seq())()
      case f@Fold(acc) =>
        val if1 = If(act1, Seqn(Seq(f), Seq())(), skip)()
        val if2 = If(act2, Seqn(Seq(
          Fold(PredicateAccessPredicate(
            PredicateAccess(acc.loc.args.map(a => translatePrime(a, p1, p2)),
              acc.loc.predicateName)(), translatePrime(acc.perm, p1, p2))())(f.pos, f.info, f.errT)
        ), Seq())(), skip)()
        val (lowFunc, lhs) = getPredicateLowFuncExp(acc.loc.predicateName, ctx)
        val assert: Stmt = lowFunc match {
          case Some(func) =>
            val et = ErrTrafo({case AssertFailed(_,_,_) => errors.FoldFailed(f, SIFFoldNotLow(f))})
            Assert(Implies(
              lhs,
              FuncApp(func.copy()(func.pos, func.info, errT = et),
                acc.loc.args ++ acc.loc.args.map(a => translatePrime(a, p1, p2)))()
            )())(f.pos, f.info, errT = et)
          case None => skip
        }
        Seqn(Seq(if1, if2, assert), Seq())()
      case r: SIFReturnStmt => {
        // TODO
        val (first, second) = translateStmtPartial(r).asInstanceOf[(Seqn, Seqn)]
        val r1 = If(act1, first, skip)()
        val r2 = If(act2, second, skip)()
        Seqn(Seq(r1, r2, incrementTime(p1, p2)), Seq())()
      }
      case b@SIFBreakStmt() => {
        // TODO
        translateAssignment(ctrlVars.break1r.get, TrueLit()(),
          ctrlVars.break2r.get, TrueLit()(), b)
      }
      case c@SIFContinueStmt() => translateAssignment(ctrlVars.cont1r.get, TrueLit()(),
        ctrlVars.cont2r.get, TrueLit()(), c)
      case tryCatch: SIFTryCatchStmt => translateTryCatchStmt(tryCatch, ctx)
      case SIFRaiseStmt(assignment) =>
        var stmts = Seq[Stmt]()
        val assign1 = assignment match {
          case Some(a) => Some(LocalVarAssign(translateNormal(a.lhs, p1, p2),
            translateNormal(a.rhs, p1, p2))())
          case None => None
        }
        val assign2 = assignment match {
          case Some(a) => Some(LocalVarAssign(translatePrime(a.lhs, p1, p2),
            translatePrime(a.rhs, p1, p2))())
          case None => None
        }
        stmts :+= If(act1,
          Seqn(Seq(assign1, Some(LocalVarAssign(ctrlVars.except1r.get, TrueLit()())()))
            .collect({case Some(x) => x}), Seq())(),
          skip)()
        stmts :+= If(act2,
          Seqn(Seq(assign2, Some(LocalVarAssign(ctrlVars.except2r.get, TrueLit()())()))
            .collect({case Some(x) => x}), Seq())(),
          skip)()
        Seqn(stmts, Seq())()
      case d@SIFDeclassifyStmt(e) => Inhale(Implies(
        And(act1, act2)(), EqCmp(translateNormal(e, p1, p2), translatePrime(e, p1, p2))()
      )())(d.pos, d.info, d.errT)
      case SIFAssertNoException() =>
        val exp: Exp = if (ctrlVars.except1r.isDefined) And(
          Implies(p1, Not(ctrlVars.except1r.get)())(s.pos, s.info, s.errT),
          Implies(p2, Not(ctrlVars.except2r.get)())(s.pos, s.info, s.errT)
        )(s.pos, s.info, s.errT)
        else TrueLit()()
        Exhale(exp)(s.pos, s.info, s.errT)
      case SIFInlinedCallStmt(stmts) =>
        val newCtrlVars = createControlFlowVars(stmts)
        val inlinedCtx = TranslationContext(p1, p2, newCtrlVars, ctx.currentMethod)
        Seqn(newCtrlVars.initAssigns() :+ translateStatement(stmts, inlinedCtx), newCtrlVars.declarations())()
      case Goto(l) => {
        val varName1 = ctrlVars.labelNames.get(l).get
        val varName2 = primedNames.get(varName1).get
        val assign1 = If(act1, Seqn(Seq(LocalVarAssign(LocalVar(varName1, Bool)(), TrueLit()())()), Seq())(), Seqn(Seq(), Seq())())()
        val assign2 = If(act2, Seqn(Seq(LocalVarAssign(LocalVar(varName2, Bool)(), TrueLit()())()), Seq())(), Seqn(Seq(), Seq())())()
        Seqn(Seq(assign1, assign2), Seq())()
      }
      case lb@Label(l, _) if ctrlVars.labelNames.contains(l) => {
        val varName1 = ctrlVars.labelNames.get(l).get
        val varName2 = primedNames.get(varName1).get
        val thisAct1 = ctx.ctrlVars.activeExecNormalExceptLabel(Some(p1), varName1)
        val thisAct2 = ctx.ctrlVars.activeExecPrimeExceptLabel(Some(p2), varName2)
        val assign1 = If(thisAct1, Seqn(Seq(LocalVarAssign(LocalVar(varName1, Bool)(), FalseLit()())()), Seq())(), Seqn(Seq(), Seq())())()
        val assign2 = If(thisAct2, Seqn(Seq(LocalVarAssign(LocalVar(varName2, Bool)(), FalseLit()())()), Seq())(), Seqn(Seq(), Seq())())()
        Seqn(Seq(lb, assign1, assign2), Seq())()
      }
      case lb : Label => lb
      case p: Package => translateWandPackage(p, ctx)
      case a: Apply => translateWandApply(a, ctx)
      case other => throw new IllegalArgumentException("unexpected: " + other)
    }
  }

  def getNewVar(name: String, typ: Type) : (LocalVarDecl, LocalVar) = {
    val newName = getName(name)
    (LocalVarDecl(newName, typ)(), LocalVar(newName, typ)())
  }

  def getNewBool(name: String) : (LocalVarDecl, LocalVar) = {
    getNewVar(name, Bool)
  }

  def isRelational(e: Exp): Boolean = {
    !isUnary(e)
  }

  def isUnary(e: Exp): Boolean = {
    val relVars = e.filter{
      case _: SIFLowExp => true
      case _: SIFLowEventExp => true
      case DomainFuncApp("Low", _, _) => true
      case _ => false
    }
    relVars.isEmpty
  }

  def translateSIFExp1(e: Exp, p1: Exp, p2: Exp): Exp = {
    e match {
      case re if isRelational(e) => Implies(And(p1, p2)(), translateNormal(e, p1, p2))(e.pos, errT = fwTs(re, re))
      case _ if isUnary(e) => translateNormal(e, p1, p2)
    }
  }

  def translateSIFExp2(e: Exp, p1: Exp, p2: Exp): Exp = {
    e match {
      case re if isRelational(e) => TrueLit()(e. pos, errT = fwTs(re, re))
      case _ => translatePrime(e, p1, p2)
    }
  }

  def translateSIFLowExpComparison(l: SIFLowExp, p1: Exp, p2: Exp): Exp = {
    val primedExp = translatePrime(l.exp, p1, p2)
    l.comparator match {
      case None => EqCmp(l.exp, primedExp)(l.pos, errT = fwTs(l, l))
      case Some(str) =>
        _program.findDomainFunctionOptionally(str) match {
          case Some(df) => DomainFuncApp(df, Seq(l.exp, primedExp), l.typVarMap)(l.pos, l.info, errT = fwTs(l, l))
          case None => _program.findFunctionOptionally(str) match {
            case Some(f) => FuncApp(f, Seq(l.exp, primedExp))(l.pos, l.info, errT = fwTs(l, l))
            case None => sys.error(s"Unknown comparator $str.")
          }
        }
    }
  }

  def translateAssDefault(e: Exp, p1: Exp, p2: Exp): And = {
    And(Implies(p1, translateSIFExp1(e, p1, p2))(e.pos, errT = fwTs(e, e)),
      Implies(p2, translateSIFExp2(e, p1, p2))(e.pos, errT = fwTs(e, e)))(e.pos, errT = fwTs(e, e))
  }

  def fwTs(t: TransformableErrors, node: ErrorNode) = {
    Trafos(t.errT.eTransformations, t.errT.rTransformations, Some(node))
  }

  def translateSIFAss(e: Exp, ctx: TranslationContext, relAssertCtx: TranslationContext = null): Exp = {
    val p1 = ctx.p1
    val p2 = ctx.p2
    val relCtx = if (relAssertCtx == null) ctx else relAssertCtx
    def bothExecutions(e: Exp, pos: Position = NoPosition, info: Info = NoInfo,
                       errT: ErrorTrafo = NoTrafos): Exp = {
      Implies(And(relCtx.p1, relCtx.p2)(), e)(pos, info, errT)
    }

    e match {
      case And(e1, e2) => And(translateSIFAss(e1, ctx, relAssertCtx), translateSIFAss(e2, ctx, relAssertCtx))(e.pos, errT = fwTs(e, e))
      case i@Implies(e1, e2) if !isUnary(i) => {
        Implies(translateSIFAss(e1, ctx, relAssertCtx), translateSIFAss(e2, ctx, relAssertCtx))(e.pos, errT = fwTs(e, e))
      }
      case Implies(e1, e2) if e2.exists({
        case PredicateAccess(_, name) => predLowFuncs(name).isDefined
        case _ => false
      }) =>
        And(translateAssDefault(e, p1, p2), Implies(
          translateSIFAss(e1, ctx, relAssertCtx),
          translatePredLowFuncOnly(e2, p1, p2)
        )())(e.pos, e.info, e.errT)
      case fa@Forall(vars, triggers, exp) =>  {
        if (fa.isPure){
          for (v <- vars){
            if (primedNames.contains(v.name)){
              primedNames.remove(v.name)
            }
          }
          /*var varEqs: Exp = TrueLit()()
          val pvars = vars.map { v =>
            val primeName = getName(v.name)
            primedNames.update(v.name, primeName)
            varEqs = And(varEqs, EqCmp(v.localVar, LocalVar(primeName)(v.typ))())()
            LocalVarDecl(primedNames.get(v.name).get, v.typ)()
          }*/
          val newTriggers = triggers.map{t => Trigger(t.exps.map{e => translatePrime(e, p1, p2)})()}
          //val res = Forall(vars ++ pvars, newTriggers, Implies(varEqs, translateSIFAss(exp, p1, p2))(e.pos, errT = NodeTrafo(e)))(e.pos, errT = NodeTrafo(e))
          val res = Forall(vars, triggers ++ newTriggers,
            translateSIFAss(exp, ctx, relAssertCtx))(e.pos, errT = fwTs(e, e)).autoTrigger
          res
        } else {
          val normal = translateNormal(fa, p1, p2)
          val prime = translatePrime(fa, p1, p2)
          And(Implies(p1, normal)(e.pos, errT = fwTs(e, e)), Implies(p2, prime)(e.pos, errT = fwTs(e, e)))(e.pos, errT = fwTs(e, e))
        }
      }
      case l: SIFLowEventExp =>
        val act1 = ctx.ctrlVars.activeExecNormal(Some(p1))
        val act2 = ctx.ctrlVars.activeExecPrime(Some(p2))
        val dynCheckInfo = l.info.getUniqueInfo[SIFDynCheckInfo]
        dynCheckInfo match {
          case None => EqCmp(act1, act2)(e.pos, errT = fwTs(e, e))
          case Some(dci) => And(EqCmp(act1, act2)(e.pos, errT = fwTs(e, e)), Implies(act1,
            EqCmp(translateNormal(dci.dynCheck, p1, p2),
              translatePrime(dci.dynCheck, p1, p2))())())(e.pos, errT = fwTs(e, e))
        }
      case _: SIFLowExitExp =>
        val act1 = ctx.ctrlVars.activeExecNoContNormal(None)
        val act2 = ctx.ctrlVars.activeExecNoContPrime(None)
        Implies(And(relCtx.p1, relCtx.p2)(), EqCmp(act1, act2)(e.pos, errT = fwTs(e, e)))(e.pos, errT = fwTs(e, e))
      case l@SIFLowExp(_, _, _) =>
        val comparison = translateSIFLowExpComparison(l, relCtx.p1, relCtx.p2)
        val dynCheckInfo = l.info.getUniqueInfo[SIFDynCheckInfo]
        dynCheckInfo match {
          case None => bothExecutions(comparison, e.pos)
          case Some(dci) =>
            val inhalePart = bothExecutions(Implies(
              EqCmp(translateNormal(dci.dynCheck, relCtx.p1, relCtx.p2), translatePrime(dci.dynCheck, relCtx.p1, relCtx.p2))(), comparison
            )(), e.pos)
            if (dci.onlyDynVersion) {
              inhalePart
            } else {
              InhaleExhaleExp(inhalePart, bothExecutions(comparison, e.pos)
              )(l.pos, l.info, errT = fwTs(l, l))
            }
        }
      // for the domain method low, used e.g. for list resource
      case f@DomainFuncApp("Low", args, _) => translateSIFAss(
        SIFLowExp(args.head, None)(f.pos, f.info, f.errT), ctx, relAssertCtx)
      case pap@PredicateAccessPredicate(pred, _) =>
        val (lowFunc, lhs) = getPredicateLowFuncExp(pred.predicateName, ctx)
        lowFunc match {
          case Some(f: Function) =>
            val lowFuncApp = Implies(lhs,
              FuncApp(f, pred.args ++ pred.args.map(a => translatePrime(a, p1, p2)))(pap.pos, pap.info, pap.errT)
            )()
            val dynCheckInfo = pap.info.getUniqueInfo[SIFDynCheckInfo]
            val lowPart: Exp = dynCheckInfo match {
              case Some(dfi) =>
                val inhalePart = Implies(
                  EqCmp(translateNormal(dfi.dynCheck, p1, p2), translatePrime(dfi.dynCheck, p1, p2))(),
                  lowFuncApp
                )(e.pos, e.info, e.errT)
                if (dfi.onlyDynVersion) inhalePart
                else InhaleExhaleExp(inhalePart, lowFuncApp)(e.pos, e.info, e.errT)
              case None => lowFuncApp
            }
            And(translateAssDefault(pap, p1, p2), lowPart)(e.pos, errT = fwTs(e, e))
          case None => translateAssDefault(pap, p1, p2)
        }
      case o@Old(oldExp) => Old(translateSIFAss(oldExp, ctx, relAssertCtx))(o.pos, o.info, o.errT)
      case FuncApp(name, _) if predAllLowFuncs.values.exists(v => v.isDefined && v.get.name == name) =>
        bothExecutions(e)
      case Unfolding(predAcc, body) if !isUnary(body) => bothExecutions(Unfolding(
        translateNormal(predAcc, relCtx.p1, relCtx.p2),
        Unfolding(translatePrime(predAcc, relCtx.p1, relCtx.p2),
          translateSIFAss(body, ctx, relAssertCtx))(e.pos, e.info, e.errT))(e.pos, e.info, e.errT),
        e.pos, e.info, e.errT)
      // case w@MagicWand(left, right) => 
      // case Let(decl, e1, e2) => ???
      case _: SIFTerminatesExp => TrueLit()()
      case _ => translateAssDefault(e, p1, p2)
    }
  }

  def translatePrime[T <: Exp](e: T, p1: Exp, p2: Exp) : T = {
    e.transform{
      case d: LocalVarDecl if primedNames.contains(d.name) =>
        d.copy(name = primedNames(d.name))(d.pos, d.info, d.errT)
      case l: LocalVar if primedNames.contains(l.name) =>
        l.copy(name = primedNames(l.name))(l.pos, l.info, l.errT)
      case l: LocalVar if !primedNames.contains(l.name) => l
      case FieldAccess(rcv, field) =>
        FieldAccess(translatePrime(rcv, p1, p2), field)(e.pos)
      case f@FuncApp(name, _) if Config.primedFuncAppReplacements.keySet.contains(name) =>
        Config.primedFuncAppReplacements(name)(f, p1, p2)
      case f@FuncApp(name, args) => FuncApp(name,
        args.map(a => translatePrime(a, p1, p2)))(f.pos, f.info, f.typ, f.errT)
      case DomainFuncApp("Low", _, _) => TrueLit()()
      case df@DomainFuncApp(name, args, typVarMap) =>
        DomainFuncApp(
          name, args.map(a => translatePrime(a, p1, p2)), typVarMap)(
          df.pos, df.info, df.typ, df.domainName, df.errT)
      case pa@PredicateAccess(args, "MayJoin") => PredicateAccess(args.map(a => translatePrime(a, p1, p2)), "MayJoinP")(pa.pos, pa.info, pa.errT)
      case pa@PredicateAccess(args, name) => PredicateAccess(args.map(a => translatePrime(a, p1, p2)),
        name)(pa.pos, pa.info, pa.errT)
      case l: SIFLowExp => Implies(And(p1, p2)(), translateSIFLowExpComparison(l, p1, p2))()
      case f@ForPerm(vars, location, body) => ForPerm(vars,
        translateResourceAccess(location),
        translatePrime(body, p1, p2))(f.pos, f.info, f.errT)
    }
  }

  def translateNormal[T <: Exp](e: T, p1: Exp, p2: Exp): T = {
    e.transform{
      case l: SIFLowExp => Implies(And(p1, p2)(), translateSIFLowExpComparison(l, p1, p2))()
      case DomainFuncApp("Low", args, _) => Implies(And(p1, p2)(), translateSIFLowExpComparison(SIFLowExp(args.head)(), p1, p2))()
    }
  }

  def translateToUnary(e: Option[Exp]): Option[Exp] = {
    e match {
      case Some(x) => Some(translateToUnary(x))
      case None => None
    }
  }

  /** Translate an expression getting rid of all the relational parts. */
  def translateToUnary(e: Exp): Exp = {
    val transformed = e.transform{
      case _: SIFLowExp => TrueLit()()
      case DomainFuncApp("Low", _, _) => TrueLit()()
      case Implies(_: SIFLowExp, _: SIFLowExp) => TrueLit()()
      case i@Implies(lhs, rhs) => Implies(lhs, translateToUnary(rhs))(i.pos, i.info, i.errT)
    }
    Simplifier.simplify(transformed)
  }

  /** Translate only the relational parts of an expression. All unary parts are translated to True.
    * @param e The expression to translate.
    * @return The translation of the relational parts of `e`.
    */
  def translatePredLowFuncBody(e: Exp): Exp = {
    val translated = e match {
      case l: SIFLowExp => translateSIFLowExpComparison(l, null, null)
      case p@PredicateAccessPredicate(loc, _) =>
        val (lowFName, _, _) = predLowFuncInfo(loc.predicateName).get
        FuncApp(lowFName,
          loc.args ++ loc.args.map(a => translatePrime(a, null, null)))(
          p.pos, NoInfo, Bool, p.errT)
      case a@And(left, right) => And(translatePredLowFuncBody(left),
        translatePredLowFuncBody(right))(a.pos, a.info, a.errT)
      case o@Or(left, right) => Or(translatePredLowFuncBody(left),
        translatePredLowFuncBody(right))(o.pos, o.info, o.errT)
      case i@Implies(left, right) => Implies(And(translateNormal(left, null, null),
        translatePrime(left, null, null))(),
        translatePredLowFuncBody(right)
      )(i.pos, i.info, i.errT)
      case _ => TrueLit()()
    }
    Simplifier.simplify(translated)
  }

  def translatePredAllLowFuncBody(e: Exp): Exp = {
    val translated = e match {
      case FieldAccessPredicate(loc, _) => EqCmp(loc, translatePrime(loc, null, null))()
      case p@PredicateAccessPredicate(loc, _) =>
        if (predAllLowFuncInfo(loc.predicateName).isDefined){
          val (lowFName, _, _) = predAllLowFuncInfo(loc.predicateName).get
          FuncApp(lowFName,
            loc.args ++ loc.args.map(a => translatePrime(a, null, null)))(
            p.pos, NoInfo, Bool, p.errT)
        }else{
          TrueLit()()
        }

      case a@And(left, right) => And(translatePredAllLowFuncBody(left),
        translatePredAllLowFuncBody(right))(a.pos, a.info, a.errT)
      case o@Or(left, right) => Or(translatePredAllLowFuncBody(left),
        translatePredAllLowFuncBody(right))(o.pos, o.info, o.errT)
      case i@Implies(left, right) => Implies(And(translateNormal(left, null, null),
        translatePrime(left, null, null))(),
        translatePredAllLowFuncBody(right)
      )(i.pos, i.info, i.errT)
      case _ => TrueLit()()
    }
    Simplifier.simplify(translated)
  }

  def translatePredLowFuncOnly(e: Exp, p1: Exp, p2: Exp): Exp = {
    val translated: Exp = e match {
      case PredicateAccessPredicate(pred, _) =>
        predLowFuncs(pred.predicateName) match {
          case Some(f: Function) => Implies(And(p1, p2)(),
            FuncApp(f, pred.args ++ pred.args.map(a => translatePrime(a, p1, p2)))(e.pos, e.info, e.errT)
          )()
          case None => TrueLit()()
        }
      case a@And(left, right) => And(translatePredLowFuncOnly(left, p1, p2),
        translatePredLowFuncOnly(right, p1, p2))(a.pos, a.info, a.errT)
      case o@Or(left, right) => Or(translatePredLowFuncOnly(left, p1, p2),
        translatePredLowFuncOnly(right, p1, p2))(o.pos, o.info, o.errT)
      case i@Implies(left, right) => Implies(And(translateNormal(left, null, null),
        translatePrime(left, null, null))(),
        translatePredLowFuncOnly(right, p1, p2)
      )(i.pos, i.info, i.errT)
      case _ => TrueLit()()
    }
    Simplifier.simplify(translated)
  }

  def translateResourceAccess(ra: ResourceAccess): ResourceAccess = {
    ra match {
      case FieldAccess(rcv, field) => {
        FieldAccess(rcv, field)(ra.pos, ra.info, ra.errT)
      }
      case PredicateAccess(args, name) => {
        PredicateAccess(args, name)(ra.pos, ra.info, ra.errT)
      }
      case _ => sys.error("Unsupported")
    }
  }

  def getPredicateLowFunction(predName: String, m: Method): Option[Function] = {
    if (allLowMethods.contains(m.name) || preservesLowMethods.contains(m.name))
      predAllLowFuncs(predName)
    else
      predLowFuncs(predName)
  }

  def getPredicateLowFuncExp(predName: String, ctx: TranslationContext): (Option[Function], Exp) = {
    val lowFunc = getPredicateLowFunction(predName, ctx.currentMethod)
    lazy val act1: Exp = ctx.ctrlVars.activeExecNormal(Some(ctx.p1))
    lazy val act2: Exp = ctx.ctrlVars.activeExecPrime(Some(ctx.p2))
    lazy val isInPreservesLow: Boolean = preservesLowMethods.contains(ctx.currentMethod.name)
    lowFunc match {
      case Some(f) =>
        var lhs = And(act1, act2)()
        if (isInPreservesLow) {
          val allStateLow = translateSIFAss(allVarsAndStateLow(ctx.currentMethod, ctx.currentMethod.formalArgs,
            old = !ctx.translatingPrecond, predicateSrc = ctx.currentMethod.pres), ctx)
          lhs = And(lhs, allStateLow)()
        }
        (Some(f), lhs)
      case None => (None, TrueLit()())
    }
  }

  def simplifyConditions(in: Seq[Exp]): Seq[Exp] = {
    val simplified = in.map(e => e.transform{
      case x: Exp if x.isPure => Simplifier.simplify(x)
    })
    simplified.filter(e => !e.isInstanceOf[TrueLit])
  }

  def flattenSeqn(in: Seqn): Seqn = {
    var newDecls: Seq[Declaration] = in.scopedDecls
    val newSS: Seq[Stmt] = in.ss.flatMap({
      case s: Seqn =>
        val innerFlat = flattenSeqn(s)
        newDecls ++= innerFlat.scopedDecls
        innerFlat.ss
      case x: Stmt => Seq(x)
    })
    Seqn(newSS, newDecls)(in.pos, in.info, in.errT)
  }

  case class TranslationContext(p1: Exp, p2: Exp,
                                ctrlVars: MethodControlFlowVars,
                                currentMethod: Method,
                                translatingPrecond: Boolean = false
                               ) {}

  class MethodControlFlowVars(hasRet: Boolean, hasBreak: Boolean, hasCont: Boolean, hasExcept: Boolean, labels: Set[Label]) {
    var ret1d, ret2d, break1d, break2d, cont1d, cont2d, except1d, except2d: Option[LocalVarDecl] = None
    var ret1r, ret2r, break1r, break2r, cont1r, cont2r, except1r, except2r: Option[LocalVar] = None
    val labelRefs1 : ListBuffer[LocalVar] = new ListBuffer[LocalVar]()
    val labelDecls1 : ListBuffer[LocalVarDecl] = new ListBuffer[LocalVarDecl]()
    val labelRefs2 : ListBuffer[LocalVar] = new ListBuffer[LocalVar]()
    val labelDecls2 : ListBuffer[LocalVarDecl] = new ListBuffer[LocalVarDecl]()
    val labelNames : mutable.HashMap[String, String] = new mutable.HashMap[String, String]()

    if (hasRet)    {val t = getNewBool("ret1");    ret1d = Some(t._1);    ret1r = Some(t._2)}
    if (hasRet)    {val t = getNewBool("ret2");    ret2d = Some(t._1);    ret2r = Some(t._2)}
    if (hasBreak)  {val t = getNewBool("break1");  break1d = Some(t._1);  break1r = Some(t._2)}
    if (hasBreak)  {val t = getNewBool("break2");  break2d = Some(t._1);  break2r = Some(t._2)}
    if (hasCont)   {val t = getNewBool("cont1");   cont1d = Some(t._1);   cont1r = Some(t._2)}
    if (hasCont)   {val t = getNewBool("cont2");   cont2d = Some(t._1);   cont2r = Some(t._2)}
    if (hasExcept) {val t = getNewBool("except1"); except1d = Some(t._1); except1r = Some(t._2)}
    if (hasExcept) {val t = getNewBool("except2"); except2d = Some(t._1); except2r = Some(t._2)}
    if (hasRet)    primedNames.update(ret1r.get.name, ret2r.get.name)
    if (hasBreak)  primedNames.update(break1r.get.name, break2r.get.name)
    if (hasCont)   primedNames.update(cont1r.get.name, cont2r.get.name)
    if (hasExcept) primedNames.update(except1r.get.name, except2r.get.name)
    for (label <- labels){
      val t1 = getNewBool(label.name + "1")
      labelRefs1.append(t1._2)
      labelDecls1.append(t1._1)
      labelNames.update(label.name, t1._2.name)
      val t2 = getNewBool(label.name + "2")
      labelRefs2.append(t2._2)
      labelDecls2.append(t2._1)
      primedNames.update(t1._2.name, t2._2.name)
    }

    def declarations(): Seq[LocalVarDecl] = {
      Seq(ret1d, ret2d, break1d, break2d, cont1d, cont2d, except1d, except2d)
        .filter(v => v.isDefined)
        .map(v => v.get) ++ labelDecls1 ++ labelDecls2
    }

    def initAssigns(): Seq[Stmt] = {
      (Seq(ret1r, ret2r, break1r, break2r, cont1r, cont2r, except1r, except2r)
        .filter(v => v.isDefined)
        .map(v => LocalVarAssign(v.get, FalseLit()())())) ++
      (labelRefs1 ++ labelRefs2).map(v => LocalVarAssign(v, FalseLit()())())
    }

    private def conjoinVars(s: Seq[Exp]): Option[Exp] = {
      val negations: Seq[Exp] = s.map(x => Not(x)())
      if (negations.nonEmpty)
        Some(negations.reduceRight[Exp]((x, y) => And(x, y)()))
      else
        None
    }

    private def activeExecHelper(p: Option[Exp], s: Seq[Exp]): Exp = {
      val controls: Option[Exp] = conjoinVars(s)
      val expressions: Seq[Exp] = Seq(p, controls).collect({case Some(x) => x})
      expressions match {
        case Nil => TrueLit()()
        case Seq(head) => head
        case _ => expressions.reduceRight[Exp]((x, y) => And(x, y)())
      }
    }

    def removeOptions(s: Seq[Option[Exp]]) : Seq[Exp] = {
      s.filter(v => v.isDefined).map(v => v.get)
    }

    def activeExecNormalExceptLabel(p1: Option[Exp], labelName: String): Exp = {
      activeExecHelper(p1, removeOptions(Seq(ret1r, break1r, cont1r, except1r)) ++ labelRefs1.filter(v => !v.name.equals(labelName)))
    }

    def activeExecPrimeExceptLabel(p2: Option[Exp], labelNamePrime: String): Exp = {
      activeExecHelper(p2, removeOptions(Seq(ret2r, break2r, cont2r, except2r)) ++ labelRefs2.filter(v => !v.name.equals(labelNamePrime)))
    }

    def activeExecNormal(p1: Option[Exp]): Exp = {
      activeExecHelper(p1, removeOptions(Seq(ret1r, break1r, cont1r, except1r)) ++ labelRefs1)
    }
    def activeExecPrime(p2: Option[Exp]): Exp = {
      activeExecHelper(p2, removeOptions(Seq(ret2r, break2r, cont2r, except2r)) ++ labelRefs2)
    }

    def activeExecNoContNormal(p1: Option[Exp]): Exp = {
      activeExecHelper(p1, removeOptions(Seq(ret1r, break1r, except1r)) ++ labelRefs1)
    }
    def activeExecNoContPrime(p2: Option[Exp]): Exp = {
      activeExecHelper(p2, removeOptions(Seq(ret2r, break2r, except2r)) ++ labelRefs2)
    }
  }

  object EmptyControlFlowVars {
    def apply(): MethodControlFlowVars = {
      new MethodControlFlowVars(false, false, false, false, Set())
    }
  }
}

object SIFExtendedTransformer extends SIFExtendedTransformer
