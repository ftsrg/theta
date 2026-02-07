/*
 *  Copyright 2025-2026 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionRuleBuilder.RefineryExpr.ExprType.NON_POINTER
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionRuleBuilder.RefineryExpr.ExprType.POINTER
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder.Companion.ENVIRONMENT
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder.Companion.refinerified
import hu.bme.mit.theta.analysis.algorithm.refinery.RefineryTransitionSystemBuilder.Companion.refineryType
import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.*
import hu.bme.mit.theta.core.type.abstracttype.AddExpr
import hu.bme.mit.theta.core.type.abstracttype.EqExpr
import hu.bme.mit.theta.core.type.abstracttype.ModExpr
import hu.bme.mit.theta.core.type.abstracttype.NeqExpr
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.IteExpr
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.booltype.*
import hu.bme.mit.theta.core.type.booltype.BoolExprs.Not
import hu.bme.mit.theta.core.type.inttype.IntExprs.Int
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import tools.refinery.logic.term.NodeVariable
import tools.refinery.logic.term.Variable
import tools.refinery.logic.term.intinterval.IntInterval
import tools.refinery.logic.term.intinterval.IntIntervalDomain
import tools.refinery.logic.term.truthvalue.TruthValue
import tools.refinery.logic.term.truthvalue.TruthValueDomain
import tools.refinery.store.dse.modification.actions.ModificationActionLiterals
import tools.refinery.store.dse.transition.actions.ActionLiterals

data class RefineryRule(
  val name: String,
  val parameters: List<Pair<String, NodeVariable>> = listOf(),
  val preConditionClauses: Set<String>,
  val helperQueries: Set<String> = setOf(),
  val actionParameters: List<NodeVariable> = listOf(),
  val actionLiterals: List<ActionLiteralProvider>,
) {

  init {
    check(actionLiterals.isNotEmpty()) { "Action clauses cannot be empty in a Refinery rule." }
  }

  val preconditionName = "${name}_precondition"

  fun getHelpers(): String =
    """
    |${helperQueries.joinToString("\n\n")}
    |
    |pred $preconditionName(${parameters.joinToString(", ") { "${it.first} ${it.second.name}" }}) <->
    |    ${
      if (preConditionClauses.isEmpty()) "true"
      else preConditionClauses.joinToString(",\n    ")
    }.
    """
      .trimMargin()

  override fun toString(): String =
    """
    |${getHelpers()}
    |
    |rule $name(${parameters.joinToString(", ")}) <->
    |    $preconditionName(${parameters.joinToString(", ") { it.second.name } })
    |==>
    |    ${actionLiterals.joinToString(",\n    ")}.
    """
      .trimMargin()
}

abstract class RefineryTransitionRuleBuilder<T>(
  protected val variables: MutableSet<Decl<*>>,
  protected val pointers: Set<Decl<*>>,
) {

  companion object {
    val supportedOperators =
      setOf("+", "-", "*", "/", "==", "!=", "<", "<=", ">", ">=", "!", "&&", "||")
  }

  private var dereferenceCounter: Int = 0
  private var pointerArithmeticCounter: Int = 0
  private var pointerComparisonCounter: Int = 0

  protected sealed class RefineryRuleBlock {

    class Id(var id: Int) {
      override fun toString(): String = id.toString()
    }

    open lateinit var preId: Id
    open lateinit var postId: Id

    abstract val allRules: List<SingleRefineryRule>

    open fun setIds(preId: Id = Id(0), postId: Id = Id(-1)) {
      this.preId = preId
      this.postId = postId
    }
  }

  protected data class SingleRefineryRule(
    val nameProviders: Set<NameProvider> = setOf(),
    val parameters: List<Pair<String, NodeVariable>> = listOf(),
    val preConditionClauses: Set<String>,
    val helperQueries: Set<() -> String> = setOf(),
    val actionParameters: List<NodeVariable> = listOf(),
    val actionLiterals: List<ActionLiteralProvider>,
    override var preId: Id = Id(-1),
    override var postId: Id = Id(-1),
  ) : RefineryRuleBlock() {

    override val allRules
      get() = listOf(this)

    override fun setIds(preId: Id, postId: Id) {
      if (postId.id <= preId.id) {
        postId.id = preId.id + 1
      }
      super.setIds(preId, postId)
    }

    fun toRefineryRule(transitionName: String): RefineryRule {
      val name = "${transitionName}__${preId}_to_${postId}"
      nameProviders.forEach { it.name = name }
      return RefineryRule(
        name = name,
        parameters = parameters,
        preConditionClauses = preConditionClauses,
        helperQueries = helperQueries.map { it() }.toSet(),
        actionParameters = actionParameters,
        actionLiterals = actionLiterals,
      )
    }
  }

  protected class SequenceRefineryRuleBlock(val blocks: List<RefineryRuleBlock>) :
    RefineryRuleBlock() {

    init {
      check(blocks.isNotEmpty()) { "SequenceRefineryRuleBlock must contain at least one block." }
    }

    override val allRules
      get() = blocks.flatMap { it.allRules }

    override fun setIds(preId: Id, postId: Id) {
      super.setIds(preId, postId)
      for (i in 0 until blocks.size) {
        val pre = if (i == 0) preId else blocks[i - 1].postId
        val post = if (i == blocks.size - 1) postId else Id(-1)
        blocks[i].setIds(pre, post)
      }
    }
  }

  protected class NondetRefineryRuleBlock(val branches: Set<RefineryRuleBlock>) :
    RefineryRuleBlock() {

    init {
      check(branches.isNotEmpty()) { "NondetRefineryRuleBlock must contain at least one branch." }
    }

    override val allRules
      get() = branches.flatMap { it.allRules }

    override fun setIds(preId: Id, postId: Id) {
      super.setIds(preId, postId)
      branches.forEach { it.setIds(preId, postId) }
    }
  }

  /**
   * Represents an expression with preconditions, parameters and a final expression string. The
   * final expression is used when the expression is embedded in another expression. The type is
   * used to distinguish between pointer and non-pointer expressions.
   */
  protected data class RefineryExpr(
    val type: ExprType,
    val preConditionClauses: Set<String>,
    val expr: RefineryExprResult<*>,
    val parameters: Set<Pair<String, String>> = setOf(),
  ) {

    constructor(
      type: ExprType,
      preConditionClauses: Set<String>,
      expr: String,
      parameters: Set<Pair<String, String>> = setOf(),
    ) : this(type, preConditionClauses, RefineryExprResult<Nothing>(expr), parameters)

    enum class ExprType {
      POINTER,
      NON_POINTER,
    }

    companion object {

      fun single(
        type: ExprType,
        preConditionClauses: Set<String>,
        expr: String,
        parameters: Set<Pair<String, String>> = setOf(),
      ): Set<RefineryExpr> = setOf(RefineryExpr(type, preConditionClauses, expr, parameters))
    }
  }

  /** Return a set of refinery rules for the given transition. */
  abstract fun build(transition: T): Set<RefineryRule>

  protected fun Stmt.toRules(): RefineryRuleBlock {
    dereferenceCounter = 0
    pointerArithmeticCounter = 0
    pointerComparisonCounter = 0
    return when (this) {
      is AssignStmt<*> -> toRules()
      is AssumeStmt -> toRules()
      is MemoryAssignStmt<*, *, *> -> toRules()
      is SkipStmt -> SingleRefineryRule(preConditionClauses = setOf(), actionLiterals = listOf())
      is SequenceStmt ->
        SequenceRefineryRuleBlock(stmts.filter { it !is SkipStmt }.map { it.toRules() })
      else -> error("Unsupported statement in RefineryRuleBuilder: $this")
    }
  }

  private fun AssignStmt<*>.toRules(): RefineryRuleBlock {
    val name = varDecl.name.refinerified
    val env = Variable.of("env")
    return if (varDecl in pointers) {
      val pointer = "pointer_$name"
      val commonPreconditions = mutableSetOf("pointer($name, $pointer)")
      if (expr is MemoryAllocationExpr<*>) {
        val expr = expr as MemoryAllocationExpr<*>
        val pointerVar = Variable.of(pointer)
        val region = Variable.of("allocated_region")
        val base = Variable.of("allocated_base")
        val nameProvider = NameProvider { "${it}_helper" }
        val helper = { "int ${nameProvider()}() = next_address($ENVIRONMENT) + 1." }

        SingleRefineryRule(
          nameProviders = setOf(nameProvider),
          parameters = listOf("Pointer" to pointerVar),
          preConditionClauses = commonPreconditions,
          helperQueries = setOf(helper),
          actionParameters = listOf(region, base, env),
          actionLiterals =
            listOf(
              { ModificationActionLiterals.create(region) },
              {
                ActionLiterals.put(
                  getStorageSymbol("MemoryRegion::size"),
                  IntInterval.of(expr.size.toInt()),
                  region,
                )
              },
              { ActionLiterals.put(getStorageSymbol("valid"), TruthValue.TRUE, region) },
              { ActionLiterals.constant(env, getNodeId(ENVIRONMENT)) },
              {
                val type = IntIntervalDomain.INSTANCE.abstractType()
                val helperQuery = getHelperQuery(nameProvider(), type, listOf())
                ActionLiterals.putComputed(
                  getStorageSymbol("next_address"),
                  listOf(env),
                  helperQuery,
                  listOf(),
                )
              },
              { ModificationActionLiterals.create(base) },
              { ActionLiterals.put(getStorageSymbol("parts"), TruthValue.TRUE, region, base) },
              { ActionLiterals.put(getStorageSymbol("offset"), IntInterval.ZERO, base) },
              { ActionLiterals.put(getStorageSymbol("target"), TruthValue.TRUE, pointerVar, base) },
            ),
        )
      } else {
        NondetRefineryRuleBlock(
          expr
            .getPointerExpr(this)
            .map { (_, preconds, expr, _) ->
              val target = "target"
              val precondsPointer = listOf("target($expr, $target)")
              val pointerVar = Variable.of(pointer)
              val targetVar = Variable.of(target)
              SingleRefineryRule(
                parameters = listOf("Pointer" to pointerVar, "Pointable" to targetVar),
                preConditionClauses = commonPreconditions + preconds + precondsPointer,
                actionLiterals =
                  listOf {
                    ActionLiterals.put(
                      getStorageSymbol("target"),
                      TruthValue.TRUE,
                      pointerVar,
                      targetVar,
                    )
                  },
              )
            }
            .toSet()
        )
      }
    } else {
      variables.add(varDecl)
      val type =
        when (varDecl.type) {
          is IntType -> IntIntervalDomain.INSTANCE.abstractType()
          is BoolType -> TruthValueDomain.INSTANCE.abstractType()
          else -> error("Unsupported variable type in RefineryRuleBuilder: ${varDecl.type}")
        } to varDecl.type.refineryType
      NondetRefineryRuleBlock(
        expr
          .getNonPointerExpr(this)
          .map { (_, preconditions, expr, params) ->
            if (expr.domainExpr != null) {
              val parameters = params.map { (type, name) -> type to Variable.of(name) }
              SingleRefineryRule(
                parameters = parameters,
                preConditionClauses = preconditions,
                actionLiterals =
                  listOf(
                    { ActionLiterals.constant(env, getNodeId(ENVIRONMENT)) },
                    { ActionLiterals.put(getStorageSymbol(name), expr.domainExpr, env) },
                  ),
              )
            } else {
              val nameProvider = NameProvider { "${it}_helper" }
              val paramList = params.joinToString { "${it.first} ${it.second}" }
              val helper = { "${type.second} ${nameProvider()}($paramList) = $expr." }
              val parameters = params.map { (type, name) -> type to Variable.of(name) }
              SingleRefineryRule(
                nameProviders = setOf(nameProvider),
                parameters = parameters,
                preConditionClauses = preconditions,
                helperQueries = setOf(helper),
                actionLiterals =
                  listOf(
                    { ActionLiterals.constant(env, getNodeId(ENVIRONMENT)) },
                    {
                      val helperParams = parameters.map { it.second }
                      val helperQuery = getHelperQuery(nameProvider(), type.first, helperParams)
                      ActionLiterals.putComputed(
                        getStorageSymbol(name),
                        listOf(env),
                        helperQuery,
                        helperParams,
                      )
                    },
                  ),
              )
            }
          }
          .toSet()
      )
    }
  }

  private fun AssumeStmt.toRules(): RefineryRuleBlock =
    NondetRefineryRuleBlock(
      cond
        .getNonPointerExpr(this)
        .map { (_, preconditions, expr, _) ->
          SingleRefineryRule(
            preConditionClauses = preconditions + listOf(expr.toString()),
            actionLiterals = emptyList(),
          )
        }
        .toSet()
    )

  private fun MemoryAssignStmt<*, *, *>.toRules(): RefineryRuleBlock {
    val exprs = expr.toClauses()
    val derefs = deref.toClauses()
    return NondetRefineryRuleBlock(
      exprs
        .flatMap { (exprType, exprPreconditions, exprExpr, exprParams) ->
          derefs.mapNotNull { (derefType, derefPreconditions, derefExpr, _) ->
            when {
              exprType != derefType -> null

              exprType == POINTER -> {
                val derefExprVar = Variable.of(derefExpr.toString())
                val targetVar = Variable.of("target")
                val preconditions =
                  exprPreconditions + derefPreconditions + "target($exprExpr, target)"
                SingleRefineryRule(
                  parameters = listOf("Pointer" to derefExprVar, "Pointable" to targetVar),
                  preConditionClauses = preconditions,
                  actionLiterals =
                    listOf {
                      ActionLiterals.put(
                        getStorageSymbol("target"),
                        TruthValue.TRUE,
                        derefExprVar,
                        targetVar,
                      )
                    },
                )
              }

              derefType == NON_POINTER -> {
                val derefStripped = derefExpr.toString().removePrefix("value(").removeSuffix(")")
                val parameters = exprParams.map { it.first to Variable.of(it.second) }
                val derefStrippedVar =
                  parameters.find { it.second.name == derefStripped }?.second
                    ?: Variable.of(derefStripped)
                val ruleParameters = (setOf("Value" to derefStrippedVar) + parameters).toList()

                if (exprExpr.domainExpr != null) {
                  SingleRefineryRule(
                    parameters = ruleParameters,
                    preConditionClauses = exprPreconditions + derefPreconditions,
                    actionLiterals =
                      listOf {
                        ActionLiterals.put(
                          getStorageSymbol("value"),
                          exprExpr.domainExpr,
                          derefStrippedVar,
                        )
                      },
                  )
                } else {
                  val nameProvider = NameProvider { "${it}_helper" }
                  val paramList = exprParams.joinToString { "${it.first} ${it.second}" }
                  val helper = { "int ${nameProvider()}($paramList) = $exprExpr." }
                  SingleRefineryRule(
                    nameProviders = setOf(nameProvider),
                    parameters = ruleParameters,
                    preConditionClauses = exprPreconditions + derefPreconditions,
                    helperQueries = setOf(helper),
                    actionLiterals =
                      listOf {
                        val helperParams = parameters.map { it.second }
                        val type = IntIntervalDomain.INSTANCE.abstractType()
                        val helperQuery = getHelperQuery(nameProvider(), type, helperParams)
                        ActionLiterals.putComputed(
                          getStorageSymbol("value"),
                          listOf(derefStrippedVar),
                          helperQuery,
                          helperParams,
                        )
                      },
                  )
                }
              }

              else -> error("Unreachable branch.")
            }
          }
        }
        .toSet()
    )
  }

  /**
   * Converts an expression to Refinery clauses.
   *
   * @return A set of possible prepared refinery expressions (see [RefineryExpr]).
   */
  private fun Expr<*>.toClauses(): Set<RefineryExpr> =
    when (this) {
      is LitExpr<*> ->
        setOfNotNull(
          RefineryExpr(
            type = NON_POINTER,
            preConditionClauses = setOf(),
            expr =
              when (this) {
                is BoolLitExpr ->
                  if (value) RefineryExprResult("true", TruthValue.TRUE)
                  else RefineryExprResult("false", TruthValue.FALSE)
                is IntLitExpr -> RefineryExprResult(value.toString(), IntInterval.of(value.toInt()))
                else -> error("Unsupported literal expression in RefineryRuleBuilder: $this")
              },
          ),
          if (this == Int(0)) {
            RefineryExpr(type = POINTER, preConditionClauses = setOf(), expr = "nullptr")
          } else null,
        )

      is RefExpr<*> -> {
        val name = decl.name.refinerified
        if (decl in pointers) {
          val pointer = "pointer_$name"
          RefineryExpr.single(
            type = POINTER,
            preConditionClauses = setOf("pointer($name, $pointer)"),
            expr = pointer,
            parameters = setOf("Pointer" to pointer),
          )
        } else {
          variables.add(decl)
          RefineryExpr.single(
            type = NON_POINTER,
            preConditionClauses = setOf(),
            expr = "$name($ENVIRONMENT)",
          )
        }
      }

      is Dereference<*, *, *> -> {
        val derefResult = { preconditions: Set<String>, referenced: String ->
          setOf(
            RefineryExpr(
              type = POINTER,
              preConditionClauses = preconditions,
              expr = referenced,
              parameters = setOf("Pointer" to referenced),
            ),
            RefineryExpr(
              type = NON_POINTER,
              preConditionClauses = preconditions,
              expr = "value($referenced)",
              parameters = setOf("Value" to referenced),
            ),
          )
        }

        val arrayExprs =
          array.toClauses().let { r ->
            r.filter { it.type == POINTER }.ifEmpty { r } // prefer pointer expressions
          }
        val derefCount = dereferenceCounter++
        arrayExprs.flatMap { (type, basePreconditions, baseExpr, _) ->
          val region = "region_${derefCount}"
          val base = "base_${derefCount}"
          val preconditions = basePreconditions.toMutableSet()
          if (type == POINTER) {
            preconditions.add("target($baseExpr, $base)")
          } else {
            preconditions.add("address($region) == $baseExpr")
            preconditions.add("parts($region, $base)")
            preconditions.add("offset($base) == 0")
          }

          when {
            offset == Int(0) -> {
              derefResult(preconditions, base)
            }

            offset.type == Int() -> {
              val referenced = "referenced_${derefCount}"
              preconditions.add("parts($region, $base)")
              preconditions.add("parts($region, $referenced)")
              val offsetExprs = offset.getNonPointerExpr(this)
              offsetExprs.flatMap { (_, offsetPreconditions, offsetExpr, _) ->
                val preconditions = (preconditions + offsetPreconditions).toMutableSet()
                preconditions.add("offset($referenced) == offset($base) + ($offsetExpr)")
                derefResult(preconditions, referenced)
              }
            }

            else -> error("Unsupported offset expression in Dereference: ${this.offset}")
          }
        }
      }

      is AddExpr<*> -> {
        ops
          .map { it.toClauses() }
          .combinations
          .flatMap { ops ->
            val nonPointerExprWithParams =
              if (ops.any { it.type != NON_POINTER }) null
              else {
                RefineryExpr(
                  type = NON_POINTER,
                  preConditionClauses = ops.flatMap { it.preConditionClauses }.toSet(),
                  expr = ops.map { it.expr }.join("+"),
                  parameters = ops.flatMap { it.parameters }.toSet(),
                )
              }

            val pointerArithmeticSupported = ops.count { it.type == POINTER } == 1
            val pointerExprWithParams =
              if (pointerArithmeticSupported) {
                val pointerOp = ops.first { it.type == POINTER }
                val pointerPreconditions = pointerOp.preConditionClauses
                val pointer = pointerOp.expr
                val pointerParams = pointerOp.parameters
                val nonPointerOps = ops.filter { it.type != POINTER }
                val nonPointerPreconditions = nonPointerOps.flatMap { it.preConditionClauses }
                val nonPointerSum = nonPointerOps.map { it.expr }.join("+")
                val nonPointerParams = nonPointerOps.flatMap { it.parameters }.toSet()
                val pointerArithmeticCount = pointerArithmeticCounter++

                val preconditions = (pointerPreconditions + nonPointerPreconditions).toMutableSet()
                val base = "ptr_arith_base_${pointerArithmeticCount}"
                val region = "ptr_arith_region_${pointerArithmeticCount}"
                val referenced = "ptr_arith_referenced_${pointerArithmeticCount}"
                preconditions.add("target($pointer, $base)")
                preconditions.add("parts($region, $base)")
                preconditions.add("parts($region, $referenced)")
                preconditions.add("offset($referenced) == offset($base) + ($nonPointerSum)")
                RefineryExpr(
                  type = POINTER,
                  preConditionClauses = preconditions,
                  expr = referenced,
                  parameters = pointerParams + nonPointerParams,
                )
              } else null

            setOfNotNull(pointerExprWithParams, nonPointerExprWithParams)
          }
      }

      is ModExpr<*> -> {
        val lExprs = leftOp.toClauses()
        val rExprs = rightOp.toClauses()
        lExprs.flatMap { (lType, lPreconditions, lExpr, lParams) ->
          rExprs.mapNotNull { (rType, rPreconditions, rExpr, rParams) ->
            when (lType) {
              NON_POINTER if rType == NON_POINTER -> {
                RefineryExpr(
                  type = NON_POINTER,
                  preConditionClauses = lPreconditions + rPreconditions,
                  // No mod operator in Refinery
                  expr = "($lExpr) - ((($lExpr) / ($rExpr)) * ($rExpr))",
                  parameters = lParams + rParams,
                )
              }
              POINTER if rType == NON_POINTER -> {
                // skipping mod for pointers
                RefineryExpr(lType, lPreconditions, lExpr, lParams)
              }
              else -> null
            }
          }
        }
      }

      is EqExpr<*> -> equalityCheck("==")
      is NeqExpr<*> -> equalityCheck("!=")

      is AndExpr -> toNonPointerClauses("&&")
      is OrExpr -> toNonPointerClauses("||")
      is NotExpr ->
        when (val op = op) {
          is EqExpr<*> -> NeqExpr.create2(op.leftOp, op.rightOp).toClauses()
          is NeqExpr<*> -> EqExpr.create2(op.leftOp, op.rightOp).toClauses()
          else -> toNonPointerClauses("!")
        }

      is UnaryExpr<*, *> -> toNonPointerClauses()
      is BinaryExpr<*, *> -> toNonPointerClauses()
      is MultiaryExpr<*, *> -> toNonPointerClauses()

      is IteExpr<*> -> {
        val getBranchExprs = { condExprs: Set<RefineryExpr>, branchExprs: Set<RefineryExpr> ->
          condExprs.flatMap { (_, condPreconditions, condExpr, _) ->
            branchExprs.map { (type, preconds, expr, params) ->
              RefineryExpr(
                type = type,
                preConditionClauses = condPreconditions + listOf(condExpr.toString()) + preconds,
                expr = expr,
                parameters = params,
              )
            }
          }
        }

        val condExprs = cond.getNonPointerExpr(this)
        val thenExprs = then.toClauses()
        val positiveExprs = getBranchExprs(condExprs, thenExprs)

        val notCondExprs = Not(cond).getNonPointerExpr(this)
        val elseExprs = `else`.toClauses()
        val negativeExprs = getBranchExprs(notCondExprs, elseExprs)

        positiveExprs + negativeExprs
      }

      else -> error("Unsupported expression in RefineryRuleBuilder: $this")
    }.let { result: Collection<RefineryExpr> ->
      check(result.isNotEmpty()) { "At least one expression expected at $this, but got none." }
      result.toSet()
    }

  private fun List<RefineryExprResult<*>>.join(operator: String): String =
    this.joinToString(" $operator ") { "($it)" }

  private fun Expr<*>.getPointerExpr(parent: Any): Set<RefineryExpr> =
    this.toClauses()
      .filter { it.type == POINTER }
      .let {
        check(it.isNotEmpty()) {
          "Pointer expression expected at $parent, expression $this does not yield a pointer expression."
        }
        it.toSet()
      }

  private fun Expr<*>.getNonPointerExpr(parent: Any): Set<RefineryExpr> =
    this.toClauses()
      .filter { it.type == NON_POINTER }
      .let {
        check(it.isNotEmpty()) {
          "Non-pointer expression expected at $parent, expression $this does not yield a non-pointer expression."
        }
        it.toSet()
      }

  private fun BinaryExpr<*, *>.equalityCheck(operator: String): Collection<RefineryExpr> {
    val lExprs = leftOp.toClauses()
    val rExprs = rightOp.toClauses()

    return lExprs.flatMap { (lType, lPreconditions, lExpr, lParams) ->
      rExprs.mapNotNull { (rType, rPreconditions, rExpr, rParams) ->
        when {
          lType != rType -> null
          lType == NON_POINTER -> {
            RefineryExpr(
              type = NON_POINTER,
              preConditionClauses = lPreconditions + rPreconditions,
              expr = "$lExpr $operator $rExpr",
              parameters = lParams + rParams,
            )
          }

          lType == POINTER -> {
            val preconditions = (lPreconditions + rPreconditions).toMutableSet()
            val pointerComparisonCount = pointerComparisonCounter++
            val lTarget = "pointer_comp_target_left_${pointerComparisonCount}"
            val rTarget = "pointer_comp_target_right_${pointerComparisonCount}"
            preconditions.add("target(${lExpr}, $lTarget)")
            preconditions.add("target(${rExpr}, $rTarget)")
            RefineryExpr(
              type = NON_POINTER,
              preConditionClauses = preconditions,
              expr = "$lTarget $operator $rTarget",
              parameters = lParams + rParams,
            )
          }

          else -> error("Unreachable branch.")
        }
      }
    }
  }

  private fun UnaryExpr<*, *>.toNonPointerClauses(
    operator: String = operatorLabel
  ): Collection<RefineryExpr> {
    check(operator in supportedOperators) {
      "Unsupported operator '$operator' at $this in RefineryRuleBuilder."
    }
    val innerExprs = op.getNonPointerExpr(this)
    return innerExprs.map { (_, innerPreconditions, innerExpr, innerParams) ->
      RefineryExpr(
        type = NON_POINTER,
        preConditionClauses = innerPreconditions,
        expr = "$operator($innerExpr)",
        parameters = innerParams,
      )
    }
  }

  private fun BinaryExpr<*, *>.toNonPointerClauses(
    operator: String = operatorLabel
  ): Collection<RefineryExpr> {
    check(operator in supportedOperators) {
      "Unsupported operator '$operator' at $this in RefineryRuleBuilder."
    }
    val lExprs = leftOp.getNonPointerExpr(this)
    val rExprs = rightOp.getNonPointerExpr(this)
    return lExprs.flatMap { (_, lPreconditions, lExpr, lParams) ->
      rExprs.map { (_, rPreconditions, rExpr, rParams) ->
        RefineryExpr(
          type = NON_POINTER,
          preConditionClauses = lPreconditions + rPreconditions,
          expr = "($lExpr) $operator ($rExpr)",
          parameters = lParams + rParams,
        )
      }
    }
  }

  private fun MultiaryExpr<*, *>.toNonPointerClauses(
    operator: String = operatorLabel
  ): Collection<RefineryExpr> {
    check(operator in supportedOperators) {
      "Unsupported operator '$operator' at $this in RefineryRuleBuilder."
    }
    return ops
      .map { it.getNonPointerExpr(this) }
      .combinations
      .map { ops ->
        RefineryExpr(
          type = NON_POINTER,
          preConditionClauses = ops.flatMap { it.preConditionClauses }.toSet(),
          expr = ops.map { it.expr }.join(operator),
          parameters = ops.flatMap { it.parameters }.toSet(),
        )
      }
  }

  private inline val <T> List<Set<T>>.combinations: Set<List<T>>
    get() =
      fold(listOf(listOf<T>())) { acc, set -> acc.flatMap { prefix -> set.map { prefix + it } } }
        .toSet()
}
