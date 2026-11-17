/*
 *  Copyright 2026 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

package hu.bme.mit.theta.xcfa.analysis.oc

import hu.bme.mit.theta.analysis.algorithm.oc.*
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.*
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.*
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.solver.SolverStatus
import tools.refinery.generator.InvalidProblemException
import tools.refinery.generator.UnsatisfiableProblemException
import tools.refinery.generator.standalone.StandaloneRefinery

internal class XcfaRefineryOcChecker(
  private val solverStrategy: RefinerySolverStrategy = RefinerySolverStrategy.DEFAULT
) : XcfaOcChecker {


  private var currentStatus: SolverStatus? = null
  private var baseRefineryCode: String = ""
  override val status: SolverStatus?
    get() = currentStatus
  private var helperCount = 0
  override var model: Valuation? = null

  override fun initialize(eg: XcfaToEventGraph.EventGraph) {
    // see XcfaSmtOcChecker for reference on what needs to be done in this initialization

    // build the refinery metamodel here
    // add property violation constraints, branching conditions
    // add event value assignment constraints
    // add rf-related constraints to the refinery problem here

    // do not add po and ws relation constraints here!

    val helperScripts = mutableSetOf<String>()
    guardGroupNames.clear()
    val (eventsCode, rfPredicatesCode) = generateEvents(eg)

    baseRefineryCode = buildString {
      if (solverStrategy != RefinerySolverStrategy.DEFAULT) {
        appendLine("import builtin::theory::z3.")
        appendLine("#z3SolverStrategy(\"${solverStrategy.name}\").")
        appendLine()
      }
      append(generateMetamodel())
      append(eventsCode)
      append(generateRelations(eg))
      append(rfPredicatesCode)
      append(generateErrors(eg)) // A hibáknak is lehetnek helperei

      if (helperScripts.isNotEmpty()) {
        append("\n% --- Helper Functions ---\n")
        helperScripts.forEach { appendLine(it) }
      }
    }

    //println("--- REFINERY CODE ---")
    //println(baseRefineryCode)
    //println("-------------------------------")
  }

  private fun generateMetamodel(): String {
    return """
            import builtin::strategy.
            
            abstract class Event {
                int value
            }
            
            pred guard(Event e).
            
            class Read extends Event.
            class Write extends Event.
            
            !exists(Read::new).
            !exists(Write::new).
            
            @decide(false)
            pred hb(Event a, Event b).
            
            pred po(Event a, Event b).
            default !po(*, *). 
            
            pred rf(Write w, Read r).
            default !rf(*, *).
            
            pred ws(Write w1, Write w2).
            default !ws(*, *).
            
            propagation rule rfIsHb(Write w, Read r) <->
                rf(w, r) ==> hb(w, r).
            propagation rule notHbIsNotRf(Write w, Read r) <->
                !hb(w, r) ==> !rf(w, r).
                
            propagation rule poIsHb(Event a, Event b) <->
                po(a, b) ==> hb(a, b).
            propagation rule notHbIsNotPo(Event a, Event b) <->
                !hb(a, b) ==> !po(a, b).
                
            propagation rule wsIsHb(Write w1, Write w2) <->
                ws(w1, w2) ==> hb(w1, w2).
            propagation rule notHbIsNotWs(Write w1, Write w2) <->
                !hb(w1, w2) ==> !ws(w1, w2).
                
            propagation rule hbAntySymmetric(Event a, Event b) <->
                hb(a, b) ==> !hb(b, a).
            
            error pred cycle(Event e) <-> hb(e, e).
            
            propagation rule hbNotReflexive(Event e)
                ==> !hb(e, e).
            
            propagation rule hbTransitive(Event a, Event c) <->
                hb(a, b), hb(b, c) ==> hb(a, c).
                
            pred wsInactive(Write w1, Write w2) <->
                !guard(w1) ; !guard(w2).
            
            error pred wsViolation(Write w1, Write w2) <->
                ws(w1, w2),
                wsInactive(w1, w2).
            
            pred rfDisabledOrNotEqual(Write w, Read r) <->
                value(w) != value(r) ;
                !guard(w) ; 
                !guard(r).
            
            error pred rfViolation(Write w, Read r) <->
                rf(w, r), 
                rfDisabledOrNotEqual(w, r).
            
            propagation rule rfVal(Write w, Read r) <->
                rf(w, r)
            ==>
                guard(w), guard(r),
                value(w): value(r), value(r): value(w),
                assert value(w) == value(r).
            
            propagation rule notRf1(Write w, Read r) <->
                !guard(w) ==> !rf(w, r).
            
            propagation rule notRf2(Write w, Read r) <->
                !guard(r) ==> !rf(w, r).
            
            propagation rule notRf3(Write w, Read r) <->
                value(w) != value(r) ==> !rf(w, r).
            
            error pred readFromSeveralWriters(Read r, Write w1, Write w2) <->
                rf(w1, r), rf(w2, r), w1 != w2.
            
            propagation rule readFromSeveralWritesProp(Read r, Write w2) <->
                rf(w1, r), w1 != w2 ==> !rf(w2, r).
                
            error pred rfSome(Read r) <->
                guard(r), !rf(_, r).
            
            error pred fromReadViolation(Write w1, Write w2, Read r) <->
                rf(w1, r), ws(w1, w2), hb(w2, r).
            
            propagation rule fromReadPropagation1(Write w2, Read r) <->
                rf(w1, r), ws(w1, w2) ==> hb(r, w2).
            
            propagation rule fromReadPropagation2(Write w1, Write w2) <->
                rf(w1, r), hb(w2, r) ==> !ws(w1, w2).
            
            propagation rule fromReadPropagation3(Write w1, Read r) <->
                ws(w1, w2), hb(w2, r) ==> !rf(w1, r).
                
            shadow pred otherRfSource(Write excluded, Read r) <->
                may(rf(w, r)), w != excluded.
                
            propagation rule rfSomeRule(Write w, Read r) <->
                may(rf(w, r)), !otherRfSource(w, r), guard(r) ==> rf(w, r).
        """.trimIndent()
  }



  /** Maps a [RefExpr] to the `value(<refineryId>)` refinery term of the referenced event, or null. */
  private fun Expr<*>.asEventValueTerm(
    events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>
  ): String? {
    if (this !is RefExpr<*>) return null
    val constDecl = decl as? IndexedConstDecl<*> ?: return null
    val targetEvent = events[constDecl.varDecl]?.values?.firstNotNullOfOrNull { list ->
      list.find { it.const == constDecl }
    } ?: return null
    return "value(${targetEvent.refineryId})"
  }

  private fun Expr<*>.toRefineryActionOrAssert(
    events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>,
    helperScripts: MutableSet<String>,
    identifier: String
  ): String {
    if (this is EqExpr<*>) {
      val left = leftOp
      val right = rightOp

      val refExpr = when {
        left is RefExpr<*> && right.asConstant != null -> left
        right is RefExpr<*> && left.asConstant != null -> right
        else -> null
      }
      val constant = when {
        left is RefExpr<*> -> right.asConstant
        right is RefExpr<*> -> left.asConstant
        else -> null
      }
      if (refExpr != null && constant != null) {
        val constDecl = refExpr.decl as IndexedConstDecl<*>
        val targetEvent = events[constDecl.varDecl]?.values?.firstNotNullOfOrNull { list ->
          list.find { it.const == constDecl }
        }
        if (targetEvent != null) {
          return "value(${targetEvent.refineryId}): $constant"
        }
      }

      val leftTerm = left.asEventValueTerm(events)
      val rightTerm = right.asEventValueTerm(events)
      if (leftTerm != null || rightTerm != null) {
        val leftExpr = left.toRefineryExpr(events, helperScripts, identifier)
        val rightExpr = right.toRefineryExpr(events, helperScripts, identifier)
        val actions = buildList {
          if (leftTerm != null) add("$leftTerm: $rightExpr")
          if (rightTerm != null) add("$rightTerm: $leftExpr")
        }
        return (actions + "assert $leftExpr == $rightExpr").joinToString(",\n\t")
      }
    }
    return "assert ${this.toRefineryExpr(events, helperScripts, identifier)}"
  }

  private fun generateEvents(eg: XcfaToEventGraph.EventGraph): Pair<String, String> {
    val sb = StringBuilder("\n% Events\n")
    val rfPredicatesSb = StringBuilder("\n% Possible Read-From Predicates\n")

    val guardGroups = LinkedHashMap<Set<Expr<BoolType>>, MutableList<XcfaEvent>>()

    eg.events.values.flatMap { it.values }.flatten().forEach { event ->
      val valueExpr = event.assignment
      val helperScripts = mutableSetOf<String>()
      val default = {
        sb.appendLine("error pred ${event.refineryId}ValueError() <->\n" +
          "\t!(${valueExpr!!.toRefineryExpr(eg.events, helperScripts, event.refineryId)}).\n\n" +
          "propagation rule ${event.refineryId}ValueRule() <->\n" +
          "\ttrue\n" +
          "==>\n" +
          "\t${valueExpr.toRefineryActionOrAssert(eg.events, helperScripts, event.refineryId)}.")
      }
      when(valueExpr) {
        null, is TrueExpr -> {}
        is EqExpr<*> -> {
          val constantValue = valueExpr.getBinaryRefConstantRelationConstant(event)
          if (constantValue != null) {
            sb.appendLine("value(${event.refineryId}): $constantValue.")
          } else {
            default()
          }
        }
        is AndExpr -> {
          var added = false
          if (valueExpr.ops.size == 2) {
            val geq = valueExpr.ops.find { it is GeqExpr<*> } as? GeqExpr<*>
            val leq = valueExpr.ops.find { it is LeqExpr<*> } as? LeqExpr<*>
            if (geq != null && leq != null) {
              val geqConst = geq.getBinaryRefConstantRelationConstant(event)
              val leqConst = leq.getBinaryRefConstantRelationConstant(event)
              if (geqConst != null && leqConst != null) {
                sb.appendLine("value(${event.refineryId}): ${geqConst}..${leqConst}.")
                added = true
              }
            }
          }
          if (!added) default()
        }
        else -> default()
      }

      sb.appendLine("${if (event.type == EventType.READ) "Read" else "Write" }(${event.refineryId}).")

      sb.appendLine("atom ${event.refineryId}.")
      if (event.guard.isEmpty()) {
        sb.appendLine("guard(${event.refineryId}).")
      } else {
        guardGroups.getOrPut(event.guard) { mutableListOf() }.add(event)
      }

      helperScripts.forEach {
        sb.appendLine(it)
      }
    }

    generateGuardGroups(eg, guardGroups, sb)

    eg.rfs.forEach { (v, list) ->
      list
        .groupBy { it.to }
        .forEach { (event, rfs) ->
          rfs.forEach { rf ->
            // TODO rf-val
          }

          rfPredicatesSb.appendLine("error pred rfSome${event.refineryId}() <->")
          val possibleRfs = rfs.joinToString(" , ") { rel ->
            "!rf(${rel.from.refineryId}, ${rel.to.refineryId})"
          }
          if (possibleRfs == "") {
            rfPredicatesSb.appendLine("\tguard(${event.refineryId}).")
          } else {
            rfPredicatesSb.appendLine("\tguard(${event.refineryId}) , $possibleRfs.")
          }
        }
    }

    return Pair(sb.toString(), rfPredicatesSb.toString())
  }

  /** Refinery predicate names of the already encoded guard groups, keyed by their conjunct set. */
  private val guardGroupNames = HashMap<Set<Expr<BoolType>>, String>()

  /**
   * Encodes each distinct guard (set of conjuncts) as a nullary base predicate `guardGroupN()`.
   *
   * - Every conjunct is encoded exactly once, as its own single-conjunct group, which is linked to
   *   the conjunct's expression.
   * - A guard with several conjuncts is the conjunction of the largest already encoded group that
   *   is a proper subset of it, plus the conjunct groups of its remaining conjuncts. Guards are
   *   processed in increasing size so that such subsets are encoded first.
   * - Events are tied to the group of their guard through a `guardGroupNMember(Event e)` relation.
   */
  private fun generateGuardGroups(
    eg: XcfaToEventGraph.EventGraph,
    guardGroups: Map<Set<Expr<BoolType>>, List<XcfaEvent>>,
    sb: StringBuilder,
  ) {
    sb.appendLine("\n% Guard groups")
    fun group(guard: Set<Expr<BoolType>>) = guardGroup(guard, eg, sb)

    guardGroups.entries
      .sortedBy { it.key.size }
      .forEach { (guard, members) ->
        val name = group(guard)
        val member = "${name}Member"
        sb.appendLine("pred $member(Event e).")
        sb.appendLine("default !$member(*).")
        members.forEach { sb.appendLine("$member(${it.refineryId}).") }
        sb.appendLine(
          "error pred ${member}Error(Event e) <->\n" +
            "\t$member(e) , guard(e) , !$name() ;\n" +
            "\t$member(e) , !guard(e) , $name()."
        )
        sb.appendLine(
          "propagation rule ${member}_pos(Event e) <->\n\t$member(e) , $name() ==> guard(e).\n" +
            "propagation rule ${member}_neg(Event e) <->\n\t$member(e) , !$name() ==> !guard(e).\n" +
            "propagation rule ${member}_up() <->\n\t$member(e) , guard(e) ==> $name().\n" +
            "propagation rule ${member}_down() <->\n\t$member(e) , !guard(e) ==> !$name()."
        )
      }
  }

  /** Returns the group predicate of a single conjunct, encoding it first if needed. */
  private fun conjunctGroup(
    conjunct: Expr<BoolType>,
    eg: XcfaToEventGraph.EventGraph,
    sb: StringBuilder,
  ): String =
    guardGroupNames[setOf(conjunct)]
      ?: run {
        val name = "guardGroup${guardGroupNames.size}"
        guardGroupNames[setOf(conjunct)] = name
        val helperScripts = mutableSetOf<String>()
        val cond = conjunct.toRefineryExpr(eg.events, helperScripts, name)
        val action = conjunct.toRefineryActionOrAssert(eg.events, helperScripts, name)
        sb.appendLine("pred $name().")
        sb.appendLine(
          "error pred ${name}Error() <->\n" +
            "\t$name() , !($cond) ;\n" +
            "\t!$name() , ($cond)."
        )
        sb.appendLine("propagation rule ${name}_pos() <->\n\t$name() ==> $action.")
        sb.appendLine("propagation rule ${name}_neg() <->\n\t!$name() ==> assert !($cond).")
        helperScripts.forEach { sb.appendLine(it) }
        name
      }

  /**
   * Splits a guard (non-empty conjunct set) into already encoded group predicates whose conjunction
   * is the guard, without encoding a new composite group for it: the group of the guard itself if
   * it exists, otherwise the largest encoded proper subset group plus the conjunct groups of the
   * remaining conjuncts.
   */
  private fun guardParts(
    guard: Set<Expr<BoolType>>,
    eg: XcfaToEventGraph.EventGraph,
    sb: StringBuilder,
  ): List<String> {
    guardGroupNames[guard]?.let {
      return listOf(it)
    }
    if (guard.size == 1) return listOf(conjunctGroup(guard.first(), eg, sb))
    val base =
      guardGroupNames.keys
        .filter { it.size > 1 && it.size < guard.size && guard.containsAll(it) }
        .maxByOrNull { it.size }
    return buildList {
      base?.let { add(guardGroupNames.getValue(it)) }
      (guard - base.orEmpty()).forEach { add(conjunctGroup(it, eg, sb)) }
    }
  }

  /** Returns the group predicate of a guard (non-empty conjunct set), encoding it first if needed. */
  private fun guardGroup(
    guard: Set<Expr<BoolType>>,
    eg: XcfaToEventGraph.EventGraph,
    sb: StringBuilder,
  ): String {
    val parts = guardParts(guard, eg, sb)
    if (guard in guardGroupNames) return guardGroupNames.getValue(guard)
    val partAtoms = parts.map { "$it()" }

    val name = "guardGroup${guardGroupNames.size}"
    guardGroupNames[guard] = name
    sb.appendLine("pred $name().")
    sb.appendLine(
      "error pred ${name}Error() <->\n\t" +
        (partAtoms.map { "$name() , !$it" } + "!$name() , ${partAtoms.joinToString(" , ")}")
          .joinToString(" ;\n\t") +
        "."
    )
    sb.appendLine(
      "propagation rule ${name}_pos() <->\n\t$name() ==> ${partAtoms.joinToString(" , ")}."
    )
    sb.appendLine(
      "propagation rule ${name}_all() <->\n\t${partAtoms.joinToString(" , ")} ==> $name()."
    )
    partAtoms.forEachIndexed { i, part ->
      sb.appendLine("propagation rule ${name}_neg$i() <->\n\t!$part ==> !$name().")
    }
    return name
  }

  private fun generateRelations(eg: XcfaToEventGraph.EventGraph): String {
    val sb = StringBuilder("\n% Relations\n")

    eg.pos.forEach { rel ->
        sb.append("po(${rel.from.refineryId}, ${rel.to.refineryId}).\n")
    }

    eg.rfs.forEach { (varDecl, relations) ->
        relations.forEach { rel ->
            sb.append("?rf(${rel.from.refineryId}, ${rel.to.refineryId}).\n")
        }
    }

    eg.wss.forEach { (varDecl, relations) ->
      relations.forEach { rel ->
        sb.append("?ws(${rel.from.refineryId}, ${rel.to.refineryId}).\n")
      }
    }

    return sb.toString()
  }

  /**
   * Encodes that at least one violation is reachable. The violation guards (an OR over violations,
   * each an OR over the guards of the incoming paths) are flattened into a list of disjunct guards,
   * each encoded via (possibly shared) guard groups:
   * - a single disjunct is asserted directly by stating its group predicates as facts,
   * - multiple disjuncts become nullary helper predicates over their group predicates, at least one
   *   of which must hold.
   */
  private fun generateErrors(eg: XcfaToEventGraph.EventGraph): String {
    if (eg.violations.isEmpty()) return ""

    val sb = StringBuilder("\n% Reach errors\n")
    val disjuncts = eg.violations.flatMap { violation -> violation.guard.toGuardDisjuncts() }
    if (disjuncts.any { it.isEmpty() }) {
      sb.appendLine("% a violation is unconditionally reachable")
      return sb.toString()
    }

    val single = disjuncts.singleOrNull()
    if (single != null) {
      guardParts(single, eg, sb).forEach { sb.appendLine("$it().") }
      return sb.toString()
    }

    val errorAtoms =
      disjuncts.mapIndexed { index, disjunct ->
        val parts = guardParts(disjunct, eg, sb).map { "$it()" }
        if (parts.size == 1) {
          parts.first()
        } else {
          sb.appendLine("pred err$index() <->\n\t${parts.joinToString(" , ")}.")
          "err$index()"
        }
      }
    sb.appendLine("error pred violationNotFound() <-> ${errorAtoms.joinToString(" , ") { "!$it" }}.")

    return sb.toString()
  }

  /**
   * Splits a violation guard (`Or` of `And`s, see [XcfaToEventGraph]) into its disjuncts, each given
   * as a conjunct set. An empty set stands for `true`.
   */
  private fun Expr<BoolType>.toGuardDisjuncts(): List<Set<Expr<BoolType>>> {
    val disjuncts = if (this is OrExpr) ops else listOf(this)
    return disjuncts.map { disjunct ->
      when (disjunct) {
        is TrueExpr -> emptySet()
        is AndExpr -> disjunct.ops.filter { it !is TrueExpr }.toSet()
        else -> setOf(disjunct)
      }
    }
  }

  override fun addConflict(conflict: Reason) {
    // TODO add conflict to refinery problem, implement later...
  }

  override fun check(
    events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>,
    pos: List<Relation<XcfaEvent>>,
    ppos: BooleanGlobalRelation,
    rfs: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
    wss: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>,
  ): SolverStatus? {
    // add po and ws relation constraints here
    // run refinery on the problem

    val finalCode = buildString {
      append(baseRefineryCode)
      //append("\n% Dynamic relations from check()\n")
      // wss és pos listák stringgé konvertálása
    }
    val problem = StandaloneRefinery.getProblemLoader().loadString(finalCode)
    try {
      var generator = StandaloneRefinery.getGeneratorFactory().createGenerator(problem)

      generator.generate()
      currentStatus = SolverStatus.SAT
      println("sat")
      return SolverStatus.SAT

    } catch (e: Exception) {
      if(e is UnsatisfiableProblemException || e is InvalidProblemException){
      println(e.message)
      currentStatus = SolverStatus.UNSAT
      println("unsat")
        return SolverStatus.UNSAT
      }
      else{
        e.printStackTrace()
        return null}

    }
    return null
  }

  override fun getHappensBefore(): GlobalRelation? {
    TODO("Not yet implemented")
    // retrieve all happens-before relations from the refinery solution, if SAT, null otherwise
  }

  override fun getPropagatedClauses(): List<Reason> = emptyList()

  override fun printStatistics(logger: Logger) {
    // TODO print refinery statistics, implement later...
  }

  private val Event.refineryId: String get() = "${ if (type == EventType.WRITE) "W" else "R"}_${const.name.toRefineryString()}".replace("$", "")

  private fun String.toRefineryString() = replace(":", "_")

  private fun Expr<*>.getBinaryRefConstantRelationConstant(event: XcfaEvent): String? {
    if (ops.size != 2) return null
    val left = ops[0]
    val right = ops[1]
    return left.asConstant?.takeIf { right == event.const.ref }
      ?: right.asConstant?.takeIf { left == event.const.ref }
  }

  private val Expr<*>.asConstant: String? get() =
    when (this) {
      is PosExpr<*> -> op.asConstant
      is IntLitExpr -> value.toString()
      is BoolLitExpr -> if (value) "1" else "0"
      else -> null
    }

  private fun Expr<*>.toRefineryExpr(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    helperScripts: MutableSet<String>,
    identifier: String,
  ): String = when (this) {
    is IntLitExpr -> value.toString()
    is BoolLitExpr -> value.toString()
    is RefExpr<*> -> {
      val constDecl = decl as IndexedConstDecl<*>
      "value(${events[constDecl.varDecl]!!.values.firstNotNullOf { it.find { it.const == constDecl }}.refineryId})"
    }
    is OrExpr -> ops.joinToString("||") { "(${it.toRefineryExpr(events, helperScripts, identifier)})" }
    is AndExpr -> ops.joinToString("&&") { "(${it.toRefineryExpr(events, helperScripts, identifier)})" }
    is NotExpr -> "!(${op.toRefineryExpr(events, helperScripts, identifier)})"
    is EqExpr<*> -> "${leftOp.toRefineryExpr(events, helperScripts, identifier)} == ${rightOp.toRefineryExpr(events, helperScripts, identifier)}"
    is NeqExpr<*> -> ops.joinToString("!=") { it.toRefineryExpr(events, helperScripts, identifier)}
    is NegExpr<*> -> "-(${op.toRefineryExpr(events, helperScripts, identifier)})"
    is AddExpr<*> -> ops.joinToString("+")  { "(${it.toRefineryExpr(events, helperScripts, identifier)})" }
    is LtExpr<*> -> ops.joinToString("<") { it.toRefineryExpr(events, helperScripts, identifier)}
    is LeqExpr<*> -> ops.joinToString("<=") { it.toRefineryExpr(events, helperScripts, identifier)}
    is GtExpr<*> -> ops.joinToString(">") { it.toRefineryExpr(events, helperScripts, identifier)}
    is GeqExpr<*> -> ops.joinToString(">=") { it.toRefineryExpr(events, helperScripts, identifier)}
    is SubExpr<*> -> ops.joinToString("-")  { "(${it.toRefineryExpr(events, helperScripts, identifier)})" }
    is MulExpr<*> -> ops.joinToString("*") { "(${it.toRefineryExpr(events, helperScripts, identifier)})"}
    is IteExpr<*> -> {
      val currentHelperId = ++helperCount
      val helperName = "${identifier}_helper_$currentHelperId"

      val condStr = cond.toRefineryExpr(events, helperScripts, identifier)
      val thenStr = then.toRefineryExpr(events, helperScripts, identifier)
      val elseStr = `else`.toRefineryExpr(events, helperScripts, identifier)

      val helperDef = """
            int $helperName() = 
                $condStr -> $thenStr;
                !($condStr) -> $elseStr.
        """.trimIndent()

      helperScripts.add(helperDef)
      "$helperName()"
    }
    is PosExpr<*> -> op.toRefineryExpr(events, helperScripts, identifier)
    is ModExpr -> {
      val l = leftOp
      val r = rightOp

      if (l is IntLitExpr && l.value.toString() == "0") {
        return "0"
      }

      val leftStr = l.toRefineryExpr(events, helperScripts, identifier)
      val rightStr = r.toRefineryExpr(events, helperScripts, identifier)

      val result = "($leftStr - (($leftStr / $rightStr) * $rightStr))"
      //println("DEBUG ModExpr: $this -> converted to: $result")
      result
    }
    else -> throw UnsupportedOperationException("Unsupported expression $this in refinery expression conversion.")
  }
}
