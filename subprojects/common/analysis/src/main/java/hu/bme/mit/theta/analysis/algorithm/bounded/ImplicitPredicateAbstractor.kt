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
package hu.bme.mit.theta.analysis.algorithm.bounded

import hu.bme.mit.theta.analysis.Trace
import hu.bme.mit.theta.analysis.algorithm.mdd.varordering.Event
import hu.bme.mit.theta.analysis.expl.ExplState
import hu.bme.mit.theta.analysis.expr.ExprAction
import hu.bme.mit.theta.analysis.pred.PredPrec
import hu.bme.mit.theta.analysis.pred.PredState
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.model.ImmutableValuation
import hu.bme.mit.theta.core.model.Valuation
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.LitExpr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.anytype.PrimeExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.AndExpr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.FalseExpr
import hu.bme.mit.theta.core.type.booltype.IffExpr
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.And
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Not
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs.Or
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.PathUtils
import hu.bme.mit.theta.core.utils.indexings.VarIndexing
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory

/**
 * Implicit predicate abstraction over a [MonolithicExpr].
 *
 * The abstract relation is a disjunction of *groups* of concrete transitions (elements of the concrete
 * [MonolithicExpr.split]). A literal is *connected* to a transition when its predicate shares a
 * variable with the transition (read or written, frame conditions excluded) or with another connected
 * predicate; transitions with the same connected set form one group. In a group's disjunct only the
 * connected literals carry their definitions, every other literal is kept by the identity `v' = v`.
 * This is exact: the variables of an unconnected predicate are untouched by the transitions and
 * independent of every constrained variable, so its definition is satisfiable for either value.
 * Structurally the unconnected literal levels become identity levels of the group's MDD node, giving
 * saturation the locality it depends on, while grouping keeps transitions that would enumerate the
 * same literal levels anyway in one node instead of repeating the enumeration per transition. With
 * every literal connected to every transition this degenerates to the single monolithic node.
 */
class ImplicitPredicateAbstractor
@JvmOverloads
constructor(
  private val concreteModel: MonolithicExpr,
  /** Group the relation by connected literals; false gives the single monolithic disjunct. */
  private val splitRelation: Boolean = true,
  /** Map trace steps to the fired concrete transition; false maps every step to the whole relation. */
  private val perStepActions: Boolean = true,
) {

  private val predToLiteral = LinkedHashMap<Expr<BoolType>, VarDecl<BoolType>>()
  private val literalToPredMap = LinkedHashMap<Decl<*>, Expr<BoolType>>()
  private lateinit var currentPrec: PredPrec
  // abstract disjunct index -> indices of the concrete transitions in it, for the last abstractModel
  private var groupTransitions: List<List<Int>> = emptyList()

  val literalToPred: Map<Decl<*>, Expr<BoolType>>
    get() = literalToPredMap

  val literalsInCreationOrder: List<VarDecl<BoolType>>
    get() = predToLiteral.values.toList()

  // the variables each concrete transition reads or writes, frame conditions excluded
  private val transitionVars: List<Set<VarDecl<*>>> by lazy {
    concreteModel.split.map(::readWriteVars)
  }

  // the concrete transitions unfolded once, for the control-flow filtering of trace steps
  private val unfoldedTransitions: List<Expr<BoolType>> by lazy {
    concreteModel.split.map { PathUtils.unfold(it, VarIndexingFactory.indexing(0)) }
  }

  /** Builds the abstract [MonolithicExpr] for [prec]; reports which literals were newly created. */
  fun abstractModel(prec: PredPrec): AbstractionResult {
    currentPrec = prec
    val lambda = LinkedHashMap<VarDecl<BoolType>, Expr<BoolType>>()
    val lambdaPrime = LinkedHashMap<VarDecl<BoolType>, Expr<BoolType>>()
    val activationLiterals = ArrayList<VarDecl<BoolType>>()
    val newLiterals = ArrayList<VarDecl<BoolType>>()

    // predicates over only ctrl vars get no literal
    prec.preds
      .filter { !concreteModel.ctrlVars.containsAll(ExprUtils.getVars(it)) }
      .forEach { expr ->
        val v =
          predToLiteral.getOrPut(expr) {
            val lit = Decls.Var("v${predToLiteral.size}", BoolType.getInstance())
            literalToPredMap[lit] = expr
            newLiterals.add(lit)
            lit
          }
        activationLiterals.add(v)
        lambda[v] = IffExpr.of(v.ref, expr)
        lambdaPrime[v] =
          BoolExprs.Iff(
            Exprs.Prime(v.ref),
            ExprUtils.applyPrimes(expr, concreteModel.transOffsetIndex),
          )
      }

    // transOffsetIndex: default offset 1 (literals, ctrl vars assigned once); non-ctrl concrete vars
    // and ctrl vars assigned several times per transition keep their concrete offsets
    var indexingBuilder = VarIndexingFactory.indexingBuilder(1)
    concreteModel.vars.forEach { decl ->
      val offset = concreteModel.transOffsetIndex[decl]
      if (decl !in concreteModel.ctrlVars) {
        repeat(offset) { indexingBuilder = indexingBuilder.inc(decl) }
      } else if (offset > 1) {
        repeat(offset - 1) { indexingBuilder = indexingBuilder.inc(decl) }
      }
    }
    val transOffsetIndex = indexingBuilder.build()

    // group the concrete transitions by their connected literal set, in first-seen order
    val literalVars = activationLiterals.associateWith { ExprUtils.getVars(literalToPredMap[it]!!) }
    val groups = LinkedHashMap<Set<VarDecl<BoolType>>, MutableList<Int>>()
    val connectivity = LinkedHashMap<VarDecl<BoolType>, Int>()
    activationLiterals.forEach { connectivity[it] = 0 }
    if (splitRelation) {
      concreteModel.split.indices.forEach { i ->
        val connected = connectedLiterals(transitionVars[i], activationLiterals, literalVars)
        connected.forEach { connectivity[it] = connectivity[it]!! + 1 }
        groups.getOrPut(connected) { ArrayList() }.add(i)
      }
    } else {
      activationLiterals.forEach { connectivity[it] = concreteModel.split.size }
      // one group, every literal connected: the classic monolithic abstract relation
      groups[activationLiterals.toSet()] = concreteModel.split.indices.toMutableList()
    }
    groupTransitions = groups.values.map { it.toList() }
    // events over the connected closure: the literal levels an abstract transition node really spans
    val closureOf = HashMap<Int, Set<VarDecl<BoolType>>>()
    groups.forEach { (connected, transitions) -> transitions.forEach { closureOf[it] = connected } }
    val closureEvents: List<Event<VarDecl<*>>> =
      concreteModel.split.indices.map { i ->
        val affected: List<VarDecl<*>> =
          transitionVars[i].filter { it in concreteModel.ctrlVars } + closureOf[i]!!.toList()
        object : Event<VarDecl<*>> {
          override fun getAffectedVars(): List<VarDecl<*>> = affected
        }
      }
    val splits =
      if (!splitRelation)
        // the classic monolithic relation, over the raw transition expression
        listOf(And(listOf(And(lambda.values), And(lambdaPrime.values), concreteModel.transExpr)))
      else
        groups.map { (connected, transitions) ->
          val identity = activationLiterals.filter { it !in connected }
          And(
            listOf(
              And(connected.map { lambda[it]!! }),
              And(connected.map { lambdaPrime[it]!! }),
              Or(transitions.map { concreteModel.split[it] }),
              And(identity.map { Eq(Exprs.Prime(it.ref), it.ref) }),
            )
          )
        }
    val allLambda = And(lambda.values)

    val model =
      MonolithicExpr(
        initExpr = And(allLambda, concreteModel.initExpr),
        transExpr = if (splits.size == 1) splits[0] else Or(splits),
        propExpr = Not(And(allLambda, Not(concreteModel.propExpr))),
        transOffsetIndex = transOffsetIndex,
        vars = activationLiterals + concreteModel.ctrlVars,
        ctrlVars = concreteModel.ctrlVars,
        events =
          concreteModel.events.map {
            val originalAffectedVars = it.getAffectedVars()
            val affectedCtrlVars = originalAffectedVars.filter { v -> v in concreteModel.ctrlVars }
            val affectedActivationLiterals =
              activationLiterals.filter { v ->
                literalToPredMap[v]!!.let { pred ->
                  ExprUtils.getVars(pred).any { v2 -> v2 in originalAffectedVars }
                }
              }
            object : Event<VarDecl<*>> {
              override fun getAffectedVars(): List<VarDecl<*>> =
                affectedCtrlVars + affectedActivationLiterals
            }
          },
        explicitSplit = splits,
      )
    return AbstractionResult(model, newLiterals, connectivity, closureEvents)
  }

  /**
   * Maps an abstract trace (over activation-literal valuations) back to a predicate trace over the
   * concrete model's actions, under the prec of the last [abstractModel] call. A step whose abstract
   * action names the fired disjunct gets the concrete transitions of that group that are consistent
   * with the control valuations of the two abstract states (usually exactly one); any other step gets
   * the whole concrete relation.
   */
  fun toPredTrace(trace: Trace<ExplState, ExprAction>): Trace<PredState, ExprAction> {
    val actions =
      trace.actions.mapIndexed { k, action ->
        if (
          perStepActions &&
            action is MonolithicExprSplitAction &&
            action.index in groupTransitions.indices
        )
          concreteAction(groupTransitions[action.index], trace.states[k], trace.states[k + 1])
        else concreteModel.action()
      }
    return Trace.of(trace.states.map(this::toPredState), actions)
  }

  private fun toPredState(valuation: Valuation): PredState =
    PredState.of(
      valuation.toMap().minus(concreteModel.ctrlVars.toSet()).map {
        when ((it.value as BoolLitExpr).value) {
          true -> literalToPredMap[it.key]
          false -> currentPrec.negate(literalToPredMap[it.key])
        }
      }
    )

  /** The action of the transitions among [candidates] enabled by the control valuations of a step. */
  private fun concreteAction(candidates: List<Int>, source: ExplState, target: ExplState): ExprAction {
    val enabled = candidates.filter { ctrlConsistent(it, source.`val`, target.`val`) }
    val chosen = if (enabled.isEmpty()) candidates else enabled
    if (chosen.size == 1) return concreteModel.splitAction(chosen[0])
    val expr = Or(chosen.map { concreteModel.split[it] })
    return object : ExprAction {
      override fun toExpr(): Expr<BoolType> = expr

      override fun nextIndexing(): VarIndexing = concreteModel.transOffsetIndex
    }
  }

  /** Whether the [transition]th concrete transition survives substituting the step's ctrl values. */
  @Suppress("UNCHECKED_CAST")
  private fun ctrlConsistent(transition: Int, source: Valuation, target: Valuation): Boolean {
    val builder = ImmutableValuation.builder()
    for (ctrl in concreteModel.ctrlVars) {
      source.eval(ctrl).ifPresent {
        builder.put(ctrl.getConstDecl(0) as Decl<Type>, it as LitExpr<Type>)
      }
      target.eval(ctrl).ifPresent {
        builder.put(
          ctrl.getConstDecl(concreteModel.transOffsetIndex[ctrl]) as Decl<Type>,
          it as LitExpr<Type>,
        )
      }
    }
    return ExprUtils.simplify(unfoldedTransitions[transition], builder.build()) !is FalseExpr
  }

  /**
   * The literals connected to a transition touching [transitionVars]: those whose predicate shares a
   * variable with the transition, closed under sharing a variable with a connected predicate.
   */
  private fun connectedLiterals(
    transitionVars: Set<VarDecl<*>>,
    literals: List<VarDecl<BoolType>>,
    literalVars: Map<VarDecl<BoolType>, Set<VarDecl<*>>>,
  ): Set<VarDecl<BoolType>> {
    val connected = LinkedHashSet<VarDecl<BoolType>>()
    val reached = HashSet<VarDecl<*>>(transitionVars)
    var changed = true
    while (changed) {
      changed = false
      for (lit in literals) {
        if (lit !in connected && literalVars[lit]!!.any { it in reached }) {
          connected.add(lit)
          reached.addAll(literalVars[lit]!!)
          changed = true
        }
      }
    }
    return connected
  }

  /**
   * The variables a transition reads or writes: all variables of its non-frame conjuncts, plus every
   * variable the relation may change (offset above 0) that this transition does not frame — a
   * havoc leaves no constraint at all, so its absence from the expression means "written", not
   * "untouched".
   */
  private fun readWriteVars(transition: Expr<BoolType>): Set<VarDecl<*>> {
    val conjuncts = ArrayList<Expr<BoolType>>()
    fun collect(e: Expr<BoolType>) {
      if (e is AndExpr) e.ops.forEach(::collect) else conjuncts.add(e)
    }
    collect(transition)
    val framed = HashSet<VarDecl<*>>()
    val touched = HashSet<VarDecl<*>>()
    for (c in conjuncts) {
      val frameVar = frameEqualityVar(c)
      if (frameVar != null) framed.add(frameVar) else touched.addAll(ExprUtils.getVars(c))
    }
    for (v in concreteModel.vars) {
      if (v !in concreteModel.ctrlVars && concreteModel.transOffsetIndex[v] > 0 && v !in framed) {
        touched.add(v)
      }
    }
    return touched
  }

  /**
   * The variable of a frame condition `x = x'…'` (either side first, the unfolder's condition for a
   * variable the transition leaves untouched), or null if [e] is not one.
   */
  private fun frameEqualityVar(e: Expr<BoolType>): VarDecl<*>? {
    val (left, right) =
      when (e) {
        is EqExpr<*> -> e.leftOp to e.rightOp
        is IffExpr -> e.leftOp to e.rightOp
        else -> return null
      }
    val (leftVar, leftPrimes) = stripPrimes(left)
    val (rightVar, rightPrimes) = stripPrimes(right)
    val frame =
      leftVar != null &&
        leftVar == rightVar &&
        minOf(leftPrimes, rightPrimes) == 0 &&
        leftPrimes != rightPrimes
    return if (frame) leftVar else null
  }

  private fun stripPrimes(e: Expr<*>): Pair<VarDecl<*>?, Int> {
    var current: Expr<*> = e
    var primes = 0
    while (current is PrimeExpr<*>) {
      current = current.op
      primes++
    }
    val decl = (current as? RefExpr<*>)?.decl as? VarDecl<*>
    return decl to primes
  }
}

data class AbstractionResult(
  val model: MonolithicExpr,
  val newLiterals: List<VarDecl<BoolType>>, // creation order
  /** For every literal, the number of concrete transitions it is connected to. */
  val connectivity: Map<VarDecl<BoolType>, Int> = emptyMap(),
  /**
   * One event per concrete transition over its ctrl vars and the connected-literal closure of its
   * group (the levels its abstract transition node spans), for FORCE ordering; [model]'s own events
   * use only the literals sharing a variable with the transition.
   */
  val closureEvents: List<Event<VarDecl<*>>> = emptyList(),
)
