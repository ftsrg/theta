/*
 *  Copyright 2024 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.common.cfa.buchi.hoa

import hu.bme.mit.theta.cfa.CFA
import hu.bme.mit.theta.common.logging.Logger
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolType
import java.util.function.Consumer
import jhoafparser.ast.AtomAcceptance
import jhoafparser.ast.AtomLabel
import jhoafparser.ast.BooleanExpression
import jhoafparser.consumer.HOAConsumer
import jhoafparser.consumer.HOAConsumerException

class BuchiBuilder
internal constructor(
  private val logger: Logger,
  private val swappedExpressions: Map<String, Expr<BoolType>>,
) : HOAConsumer {

  private val builder: CFA.Builder = CFA.builder()
  private var initLocNumber: Int? = null
  private var aps: MutableList<String>? = null
  private val locations: MutableMap<Int, CFA.Loc> = HashMap()

  fun build(): CFA {
    return builder.build()
  }

  private fun getOrCreateLocation(locName: Int): CFA.Loc {
    return locations.computeIfAbsent(locName) { i: Int -> builder.createLoc(i.toString()) }
  }

  private fun apBoolExpressionToInternal(
    booleanExpression: BooleanExpression<AtomLabel>
  ): Expr<BoolType> {
    return when (booleanExpression.type) {
      BooleanExpression.Type.EXP_AND ->
        BoolExprs.And(
          apBoolExpressionToInternal(booleanExpression.left),
          apBoolExpressionToInternal(booleanExpression.right),
        )

      BooleanExpression.Type.EXP_OR ->
        BoolExprs.Or(
          apBoolExpressionToInternal(booleanExpression.left),
          apBoolExpressionToInternal(booleanExpression.right),
        )

      BooleanExpression.Type.EXP_NOT ->
        BoolExprs.Not(apBoolExpressionToInternal(booleanExpression.left))
      BooleanExpression.Type.EXP_TRUE -> BoolExprs.True()
      BooleanExpression.Type.EXP_ATOM ->
        swappedExpressions[aps!![booleanExpression.atom.toString().toInt()]]!!
      else -> BoolExprs.False()
    }
  }

  override fun parserResolvesAliases(): Boolean {
    return false
  }

  override fun notifyHeaderStart(s: String) {
    logger.write(Logger.Level.VERBOSE, "HOA consumer header: %s%n", s)
  }

  override fun setNumberOfStates(i: Int) {
    logger.write(Logger.Level.VERBOSE, "HOA automaton has %d states%n", i)
  }

  @Throws(HOAConsumerException::class)
  override fun addStartStates(list: List<Int>) {
    if (list.isEmpty()) return
    if (list.size != 1 || initLocNumber != null)
      throw HOAConsumerException("HOA automaton should have exactly 1 starting location%n")
    initLocNumber = list[0]
  }

  override fun addAlias(s: String, booleanExpression: BooleanExpression<AtomLabel>) {
    // currently does not get called by the Owl library
  }

  override fun setAPs(list: List<String>) {
    if (aps == null) aps = java.util.List.copyOf(list) else aps!!.addAll(list)
  }

  @Throws(HOAConsumerException::class)
  override fun setAcceptanceCondition(
    i: Int,
    booleanExpression: BooleanExpression<AtomAcceptance>,
  ) {
    logger.write(Logger.Level.VERBOSE, "Acceptance condition: %s%n", booleanExpression)
  }

  override fun provideAcceptanceName(s: String, list: List<Any>) {
    logger.write(Logger.Level.VERBOSE, "Acceptance name received: %s%n", s)
    list.forEach(
      Consumer { o: Any? ->
        logger.write(Logger.Level.VERBOSE, "\tobject under acceptance: %s%n", o)
      }
    )
  }

  @Throws(HOAConsumerException::class)
  override fun setName(s: String) {
    logger.write(Logger.Level.VERBOSE, "Automaton named {}%n", s)
  }

  override fun setTool(s: String, s1: String) {
    logger.write(Logger.Level.VERBOSE, "Tool named %s %s%n", s, s1)
  }

  override fun addProperties(list: List<String>) {
    if (list.isEmpty()) return
    logger.write(Logger.Level.VERBOSE, "Properties:%n")
    list.forEach(Consumer { prop: String? -> logger.write(Logger.Level.VERBOSE, "%s", prop) })
    logger.write(Logger.Level.VERBOSE, "%n")
  }

  override fun addMiscHeader(s: String, list: List<Any>) {
    // we don't really care for these yet
  }

  override fun notifyBodyStart() {
    // no action needed
  }

  override fun addState(
    i: Int,
    s: String?,
    booleanExpression: BooleanExpression<AtomLabel>?,
    list: List<Int>?,
  ) {
    getOrCreateLocation(i)
  }

  override fun addEdgeImplicit(i: Int, list: List<Int>, list1: List<Int>) {
    TODO("This should only be called for state-based acceptance which is not yet supported")
  }

  @Throws(HOAConsumerException::class)
  override fun addEdgeWithLabel(
    i: Int,
    booleanExpression: BooleanExpression<AtomLabel>,
    list: List<Int>,
    list1: List<Int>?,
  ) {
    val from = getOrCreateLocation(i)
    val to = getOrCreateLocation(list[0])
    val edge =
      builder.createEdge(from, to, Stmts.Assume(apBoolExpressionToInternal(booleanExpression)))
    if (list1 != null && !list1.isEmpty()) builder.setAcceptingEdge(edge)
  }

  override fun notifyEndOfState(i: Int) {
    // no action needed
  }

  @Throws(HOAConsumerException::class)
  override fun notifyEnd() {
    if (initLocNumber == null) throw HOAConsumerException("No initial location named")
    builder.initLoc = locations[initLocNumber]
  }

  override fun notifyAbort() {
    // never gets called yet
  }

  @Throws(HOAConsumerException::class)
  override fun notifyWarning(s: String) {
    throw HOAConsumerException(s)
  }
}
