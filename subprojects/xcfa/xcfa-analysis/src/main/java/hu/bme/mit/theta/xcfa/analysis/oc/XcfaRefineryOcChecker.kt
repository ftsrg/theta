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

import hu.bme.mit.theta.analysis.algorithm.oc.BooleanGlobalRelation
import hu.bme.mit.theta.analysis.algorithm.oc.Event
import hu.bme.mit.theta.analysis.algorithm.oc.EventType
import hu.bme.mit.theta.analysis.algorithm.oc.GlobalRelation
import hu.bme.mit.theta.analysis.algorithm.oc.Reason
import hu.bme.mit.theta.analysis.algorithm.oc.Relation
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.decl.IndexedConstDecl
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.GeqExpr
import hu.bme.mit.theta.core.type.abstracttype.GtExpr
import hu.bme.mit.theta.core.type.abstracttype.LeqExpr
import hu.bme.mit.theta.core.type.abstracttype.LtExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.abstracttype.SubExpr
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.NotExpr
import hu.bme.mit.theta.core.type.booltype.OrExpr
import hu.bme.mit.theta.core.type.booltype.TrueExpr
import hu.bme.mit.theta.core.type.inttype.IntEqExpr
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.solver.SolverStatus
import tools.refinery.generator.standalone.StandaloneRefinery

internal class XcfaRefineryOcChecker : XcfaOcChecker {


  private var currentStatus: SolverStatus? = null
  private var baseRefineryCode: String = ""
  override val status: SolverStatus?
    get() = currentStatus
  // run refinery on the problem, return SAT/UNSAT, null if not yet run
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
            class Event {
                int index
                boolean isRead
                int value
                boolean guard
            }

            pred hb(Event a, Event b).
            default !hb(*, *). 
            
            pred po(Event a, Event b).
            default !po(*, *). 
            
            pred rf(Event w, Event r).
            default !rf(*, *).

            propagation rule rfIsHb(Event w, Event r) <->
                rf(w, r) ==> hb(w, r).

            propagation rule hbTransitive(Event a, Event c) <->
                hb(a, b), hb(b, c) ==> hb(a, c).

            error pred cycle(Event e) <-> hb(e, e).

            error pred rfBadTypes(Event w, Event r) <->
                rf(w, r), (isRead(w) || !isRead(r)).

            error pred rfValuesNotEqual(Event w, Event r) <->
                rf(w, r), (value(w) != value(r)).

            error pred readFromSeveralWriters(Event r, Event w1, Event w2) <->
                rf(w1, r), rf(w2, r), w1 != w2.

        """.trimIndent()
  }

  private fun generateEvents(eg: XcfaToEventGraph.EventGraph): Pair<String, String> {
    val sb = StringBuilder("\n% Events\n")
    val rfPredicatesSb = StringBuilder("\n% Possible Read-From Predicates\n")
    eg.events.values.flatMap { it.values }.flatten().forEach { event ->
      val helperScripts = mutableSetOf<String>()
      val valueExpr = event.assignment
      //elágazás konkrét érték, tartomány, kifejezés
      when(valueExpr) {
        null -> sb.appendLine("value(${event.refineryId}): unknown.")
        //is IntLitExpr -> sb.appendLine("value(${event.refineryId}): ${valueExpr.value}.")
        //is BoolLitExpr -> if (valueExpr.value) sb.appendLine("value(${event.refineryId}): 1.")
        //                            else sb.appendLine("value(${event.refineryId}): 0.")
        is EqExpr<*> -> {
          val constantValue = when {
            valueExpr.rightOp is IntLitExpr -> (valueExpr.rightOp as IntLitExpr).value.toString()
            valueExpr.leftOp is IntLitExpr -> (valueExpr.leftOp as IntLitExpr).value.toString()
            valueExpr.rightOp is BoolLitExpr -> if ((valueExpr.rightOp as BoolLitExpr).value) "1" else "0"
            valueExpr.leftOp is BoolLitExpr -> if ((valueExpr.leftOp as BoolLitExpr).value) "1" else "0"
            else -> null
          }

          if (constantValue != null) {
            sb.appendLine("value(${event.refineryId}): $constantValue.")
          } else {
            sb.appendLine("error pred ${event.refineryId}ValueError() <-> !(${valueExpr.toRefineryExpr(eg.events, helperScripts, event.refineryId)}).\n\n" +
              "propagation rule ${event.refineryId}ValueRule() <->\n" +
              "\ttrue\n" +
              "==>\n" +
              "\tassert ${valueExpr.toRefineryExpr(eg.events, helperScripts, event.refineryId)}.")
            helperScripts.forEach {
              sb.appendLine(it)
            }
          }
        }
        is TrueExpr -> {}
        //is IntEqExpr && (leftOp.decl == event.const) -> sb.appendLine("value(${event.refineryId}): ${valueExpr.rightOp}.")
        else -> {
          sb.appendLine("error pred ${event.refineryId}ValueError() <-> !(${valueExpr.toRefineryExpr(eg.events, helperScripts, event.refineryId)}).\n\n" +
            "propagation rule ${event.refineryId}ValueRule() <->\n" +
            "\ttrue\n" +
            "==>\n" +
            "\tassert ${valueExpr.toRefineryExpr(eg.events, helperScripts, event.refineryId)}.")
          helperScripts.forEach {
            sb.appendLine(it)
          }
        }
      }

      val guardString = event.guard.joinToString(" && ") { it.toRefineryExpr(eg.events, helperScripts, event.refineryId) }

      val type = if (event.type == EventType.READ) "true" else "false"

      sb.appendLine("Event(${event.refineryId}).")
      sb.appendLine("atom ${event.refineryId}.")
      sb.appendLine("isRead(${event.refineryId}): $type.")
      //sb.appendLine("value(${event.refineryId}): $valueExprToString.")

      if (event.guard.isEmpty()) {
        sb.appendLine("guard(${event.refineryId}): true.")
      }
      else {
        sb.appendLine("pred guard${event.refineryId}() <-> guard(${event.refineryId}) == ($guardString).")
        sb.appendLine("guard${event.refineryId}().")
      }

      if (event.type == EventType.READ) {
        rfPredicatesSb.appendLine("pred rfSome${event.refineryId}() <->")
        val possibleRfs = event.possibleRFs(eg.rfs)
        if (possibleRfs == "") {
          rfPredicatesSb.appendLine("\t!guard(${event.refineryId}).")
        } else {
          rfPredicatesSb.appendLine("\t!guard(${event.refineryId}) ; $possibleRfs.")
        }
        rfPredicatesSb.appendLine("rfSome${event.refineryId}().")
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
      val guardExpr = violation.guard.toRefineryExpr(eg.events, helperScripts, currentEventId = errorId)
      sb.appendLine("pred $errorId() <-> $guardExpr.")
    }
    sb.appendLine("\npred errorReached() <-> ${errorNames.joinToString(" ; ") { "$it()" }}.")

    sb.appendLine("error pred violationNotFound() <-> !errorReached().")

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
      //kiértékelés: ha talált modellt, akkor SAT
      currentStatus = SolverStatus.SAT
      println("sat")
      return SolverStatus.SAT

    } catch (e: Exception) {
      // ha ellentmondás, vagy hiba van, akkor UNSAT
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

  private fun Expr<*>.toRefineryExpr(
    events: Map<VarDecl<*>, Map<Int, List<E>>>,
    helperScripts: MutableSet<String>,
    currentEventId: String
  ): String = when (this) {
    is IntLitExpr -> value.toString()
    is BoolLitExpr -> value.toString()
    is RefExpr<*> -> {
      val constDecl = decl as IndexedConstDecl<*>
      "value(${events[constDecl.varDecl]!!.values.firstNotNullOf { it.find { it.const == constDecl }}.refineryId})"
    }
    is OrExpr -> ops.joinToString("||") { "(${it.toRefineryExpr(events, helperScripts, currentEventId)})" }
    is AndExpr -> ops.joinToString("&&") { "(${it.toRefineryExpr(events, helperScripts, currentEventId)})" }
    is NotExpr -> "!(${op.toRefineryExpr(events, helperScripts, currentEventId)})"
    is EqExpr<*> -> "${leftOp.toRefineryExpr(events, helperScripts,currentEventId)} == ${rightOp.toRefineryExpr(events, helperScripts, currentEventId)}"
    is NeqExpr<*> -> ops.joinToString("!=") { it.toRefineryExpr(events, helperScripts, currentEventId)}
    is AddExpr<*> -> ops.joinToString("+")  { "(${it.toRefineryExpr(events, helperScripts, currentEventId)})" }
    is LtExpr<*> -> ops.joinToString("<") { it.toRefineryExpr(events, helperScripts, currentEventId)}
    is LeqExpr<*> -> ops.joinToString("<=") { it.toRefineryExpr(events, helperScripts, currentEventId)}
    is GtExpr<*> -> ops.joinToString(">") { it.toRefineryExpr(events, helperScripts, currentEventId)}
    is GeqExpr<*> -> ops.joinToString(">=") { it.toRefineryExpr(events, helperScripts, currentEventId)}
    is SubExpr<*> -> ops.joinToString("-")  { "(${it.toRefineryExpr(events, helperScripts, currentEventId)})" }
    is IteExpr<*> -> {
      val currentHelperId = ++helperCount
      val helperName = "${currentEventId}_helper_$currentHelperId"

      val condStr = cond.toRefineryExpr(events, helperScripts, currentEventId)
      val thenStr = then.toRefineryExpr(events, helperScripts, currentEventId)
      val elseStr = `else`.toRefineryExpr(events, helperScripts, currentEventId)

      val helperDef = """
            int $helperName() = 
                $condStr -> $thenStr;
                !($condStr) -> $elseStr.
        """.trimIndent()

      helperScripts.add(helperDef)
      "$helperName()"
    }
    else -> throw UnsupportedOperationException("Unsupported expression $this in refinery expression conversion.")
  }

  private fun Event.possibleRFs(rfs: Map<VarDecl<*>, Set<Relation<XcfaEvent>>>): String {
    val relevantRelations = rfs[this.const.varDecl] ?: return ""

    return relevantRelations
      .filter { it.to == this }
      .joinToString(" ; ") { rel ->
        "rf(${rel.from.refineryId}, ${rel.to.refineryId})"
      }
  }
}
