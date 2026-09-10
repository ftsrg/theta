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
import tools.refinery.generator.standalone.StandaloneRefinery

internal class XcfaRefineryOcChecker : XcfaOcChecker {


  private var currentStatus: SolverStatus? = null
  private var baseRefineryCode: String = ""
  override val status: SolverStatus?
    get() = currentStatus
  private var helperCount = 0
  override val model: Valuation?
    get() = TODO("Not yet implemented") // retrieve the model from refinery, if SAT, null otherwise

  override fun initialize(eg: XcfaToEventGraph.EventGraph) {
    // see XcfaSmtOcChecker for reference on what needs to be done in this initialization

    // build the refinery metamodel here
    // add property violation constraints, branching conditions
    // add event value assignment constraints
    // add rf-related constraints to the refinery problem here

    // do not add po and ws relation constraints here!

    val helperScripts = mutableSetOf<String>()
    val (eventsCode, rfPredicatesCode) = generateEvents(eg)

    baseRefineryCode = buildString {
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

    println("--- REFINERY CODE ---")
    println(baseRefineryCode)
    println("-------------------------------")
  }

  private fun generateMetamodel(): String {
    return """
            import builtin::strategy.
            import builtin::theory::ibex.
            
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
        """.trimIndent()
  }

  private fun generateEvents(eg: XcfaToEventGraph.EventGraph): Pair<String, String> {
    val sb = StringBuilder("\n% Events\n")
    val rfPredicatesSb = StringBuilder("\n% Possible Read-From Predicates\n")
    eg.events.values.flatMap { it.values }.flatten().forEach { event ->
      val valueExpr = event.assignment
      val helperScripts = mutableSetOf<String>()
      val default = {
        sb.appendLine("error pred ${event.refineryId}ValueError() <->\n" +
          "\t!(${valueExpr!!.toRefineryExpr(eg.events, helperScripts, event.refineryId)}).\n\n" +
          "propagation rule ${event.refineryId}ValueRule() <->\n" +
          "\ttrue\n" +
          "==>\n" +
          "\tassert ${valueExpr.toRefineryExpr(eg.events, helperScripts, event.refineryId)}.")
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
        val (guardString, assertGuard, assertNotGuard) =
          if (event.guard.size == 1) {
            event.guard.first().toRefineryExpr(eg.events, helperScripts, event.refineryId).let {
              Triple(it, "assert $it", "assert !($it)")
            }
          } else {
            val helperScriptName = "${event.refineryId}_guard_helper"
            sb.appendLine(
              """
                |pred $helperScriptName() <->
                |${'\t'}${event.guard.joinToString(" ,\n|\t") {
                  it.toRefineryExpr(eg.events, helperScripts, event.refineryId)
                }}.
              """.trimMargin()
            )
            "${helperScriptName}()".let { Triple(it, it, "!$it") }
          }
        sb.appendLine("error pred guard${event.refineryId}() <->\n" +
                      "\t!guard(${event.refineryId}) , ($guardString);\n" +
                      "\tguard(${event.refineryId}) , !($guardString).")
        // propagation rule, as well:
        sb.appendLine("propagation rule guard${event.refineryId}_pos() <->\n" +
                      "\tguard(${event.refineryId}) ==> $assertGuard." +
                      "\npropagation rule guard${event.refineryId}_neg() <->\n" +
                      "\t!guard(${event.refineryId}) ==> $assertNotGuard."
                      )
      }

      helperScripts.forEach {
        sb.appendLine(it)
      }
    }

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

  private fun generateErrors(eg: XcfaToEventGraph.EventGraph): String {
    if (eg.violations.isEmpty()) return ""

    val sb = StringBuilder("\n% Reach errors\n")
    val errorNames = mutableListOf<String>()

    eg.violations.forEachIndexed { index, violation ->
      val errorId = "err${index}_pid${violation.pid}"
      errorNames.add(errorId)
      val helperScripts = mutableSetOf<String>()
      val guardExpr = violation.guard.toTopLevelRefineryExpr(eg.events, helperScripts, identifier = errorId)
      sb.appendLine("pred $errorId() <->\n\t$guardExpr.")
      helperScripts.forEach {
        sb.appendLine(it)
      }
    }
    sb.appendLine("error pred violationNotFound() <-> ${errorNames.joinToString(" , ") { "!$it()" }}.")

    return sb.toString()
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
      currentStatus = SolverStatus.UNSAT
      println("unsat")
      return SolverStatus.UNSAT
    }
  }

  override fun getHappensBefore(): GlobalRelation? {
    TODO("Not yet implemented")
    // retrieve all happens-before relations from the refinery solution, if SAT, null otherwise
  }

  override fun getPropagatedClauses(): List<Reason> = emptyList()

  override fun printStatistics(logger: Logger) {
    // TODO print refinery statistics, implement later...
  }

  private val Event.refineryId: String get() = "${ if (type == EventType.WRITE) "W" else "R"}_${const.name.toRefineryString()}"

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

  private fun Expr<*>.toTopLevelRefineryExpr(
    events: Map<VarDecl<*>, Map<Int, List<XcfaEvent>>>,
    helperScripts: MutableSet<String>,
    identifier: String,
  ): String = when (this) {
    is AndExpr ->
      if (ops.size == 1) {
        ops.first().toTopLevelRefineryExpr(events, helperScripts, identifier)
      } else {
        ops.joinToString(" ,\n\t") { it.toRefineryExpr(events, helperScripts, identifier) }
      }
    is OrExpr ->
      if (ops.size == 1) {
        ops.first().toTopLevelRefineryExpr(events, helperScripts, identifier)
      } else {
        ops.joinToString(" ;\n\t") { it.toRefineryExpr(events, helperScripts, identifier) }
      }
    else -> toRefineryExpr(events, helperScripts, identifier)
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
    is AddExpr<*> -> ops.joinToString("+")  { "(${it.toRefineryExpr(events, helperScripts, identifier)})" }
    is LtExpr<*> -> ops.joinToString("<") { it.toRefineryExpr(events, helperScripts, identifier)}
    is LeqExpr<*> -> ops.joinToString("<=") { it.toRefineryExpr(events, helperScripts, identifier)}
    is GtExpr<*> -> ops.joinToString(">") { it.toRefineryExpr(events, helperScripts, identifier)}
    is GeqExpr<*> -> ops.joinToString(">=") { it.toRefineryExpr(events, helperScripts, identifier)}
    is SubExpr<*> -> ops.joinToString("-")  { "(${it.toRefineryExpr(events, helperScripts, identifier)})" }
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
    else -> throw UnsupportedOperationException("Unsupported expression $this in refinery expression conversion.")
  }
}
