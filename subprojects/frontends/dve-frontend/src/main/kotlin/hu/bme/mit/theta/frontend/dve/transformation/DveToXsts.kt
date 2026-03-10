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

package hu.bme.mit.theta.frontend.dve.transformation

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.*
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.*
import hu.bme.mit.theta.core.type.anytype.Exprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.booltype.SmartBoolExprs
import hu.bme.mit.theta.core.type.enumtype.EnumLitExpr
import hu.bme.mit.theta.core.type.enumtype.EnumType
import hu.bme.mit.theta.core.type.inttype.IntExprs
import hu.bme.mit.theta.core.type.inttype.IntLitExpr
import hu.bme.mit.theta.core.type.inttype.IntType
import hu.bme.mit.theta.frontend.dve.model.*
import hu.bme.mit.theta.xsts.XSTS

/** Transforms a [DveModel] into an [XSTS]. */
object DveToXsts {

  enum class PropType {
    ASSERTIONS,
    FULL_EXPLORATION,
  }

  fun transform(model: DveModel, propType: PropType = PropType.ASSERTIONS): XSTS {
    if (model.system.propertyProcessName != null)
      throw UnsupportedOperationException(
        "Property processes (Büchi/LTL liveness) are not supported."
      )
    if (model.system.type == DveSystemType.SYNC)
      throw UnsupportedOperationException(
        "Synchronous system composition (system sync) is not yet supported."
      )

    val ctx = TransformContext(model)
    ctx.build()
    val prop = ctx.buildProp(propType)

    return XSTS(
      ctx.allStateVars.toSet(),
      ctx.localVars.toSet(),
      ctx.ctrlVars.toSet(),
      NonDetStmt.of(listOf()),
      ctx.tranStmt,
      NonDetStmt.of(listOf()),
      ctx.initFormula,
      prop,
    )
  }
}

private class TransformContext(private val model: DveModel) {

  val pcVars = mutableMapOf<String, VarDecl<EnumType>>()
  val varMap = mutableMapOf<String, VarDecl<IntType>>()
  val chanVars = mutableMapOf<String, VarDecl<IntType>>()
  val dataVars = mutableListOf<VarDecl<IntType>>()

  /** Const scalar variables inlined as integer literals (not added to varMap/dataVars). */
  private val constScalars = mutableMapOf<String, Int>()

  val ctrlVars: List<VarDecl<EnumType>>
    get() = pcVars.values.toList()

  val allStateVars: List<VarDecl<*>>
    get() = pcVars.values.toList() + dataVars + chanVars.values.toList()

  val localVars: List<VarDecl<*>>
    get() = emptyList()

  lateinit var tranStmt: NonDetStmt
  lateinit var initFormula: Expr<BoolType>

  fun build() {
    declareStateVariables()
    collectConsts()
    declareDataVariables()
    declareChannelVariables()
    buildInit()
    buildTrans()
  }

  /** Evaluates all const declarations (global then per-process) into [constScalars]. */
  private fun collectConsts() {
    for (decl in model.globalVariables) collectConst(decl, null)
    for (proc in model.processes) for (decl in proc.variables) collectConst(decl, proc.name)
  }

  private fun collectConst(decl: DveVarOrArrayDecl, processName: String?) {
    when (decl) {
      is DveVarOrArrayDecl.Scalar -> {
        if (!decl.decl.isConst) return
        val init = decl.decl.initialValue
        require(init is DveExpression.LiteralExpr) {
          "Const '${decl.decl.name}' initializer must be an integer literal, got: $init"
        }
        constScalars[varKey(processName, decl.decl.name)] = init.value
      }
      is DveVarOrArrayDecl.Array -> Unit
    }
  }

  private fun declareStateVariables() {
    for (proc in model.processes) {
      val enumType = EnumType.of("${proc.name}_State", proc.states)
      val pc = Decls.Var("${proc.name}_state", enumType)
      pcVars[proc.name] = pc
    }
  }

  private fun declareDataVariables() {
    for (decl in model.globalVariables) declareVarOrArray(decl, null)
    for (proc in model.processes) for (decl in proc.variables) declareVarOrArray(decl, proc.name)
  }

  private fun declareVarOrArray(decl: DveVarOrArrayDecl, processName: String?) {
    when (decl) {
      is DveVarOrArrayDecl.Scalar -> {
        if (decl.decl.isConst) return
        val v = Decls.Var(varXstsName(processName, decl.decl.name), IntType.getInstance())
        varMap[varKey(processName, decl.decl.name)] = v
        dataVars += v
      }
      is DveVarOrArrayDecl.Array -> {
        if (decl.decl.isConst) return
        for (i in 0 until decl.decl.size) {
          val v = Decls.Var(varXstsName(processName, decl.decl.name, i), IntType.getInstance())
          varMap[varKey(processName, decl.decl.name, i)] = v
          dataVars += v
        }
      }
    }
  }

  private fun declareChannelVariables() {
    for (ch in model.channels) {
      if (ch.bufferSize > 0) {
        val countVar = Decls.Var("${ch.name}_count", IntType.getInstance())
        chanVars["${ch.name}.count"] = countVar
        for (slot in 0 until ch.bufferSize) {
          for (field in ch.typedFields.indices) {
            val sv = Decls.Var("${ch.name}_slot${slot}_field${field}", IntType.getInstance())
            chanVars["${ch.name}.slot${slot}.field${field}"] = sv
          }
        }
      }
    }
  }

  private fun buildInit() {
    val fExprs = mutableListOf<Expr<BoolType>>()

    for (proc in model.processes) {
      val pc = pcVars[proc.name]!!
      val lit = stateLit(proc.name, proc.initialState)
      fExprs += Eq(pc.ref, lit)
    }

    for (decl in model.globalVariables) initVarOrArray(decl, null, fExprs)
    for (proc in model.processes) for (decl in proc.variables) initVarOrArray(
      decl,
      proc.name,
      fExprs,
    )

    for (ch in model.channels) {
      if (ch.bufferSize > 0) {
        val cnt = chanVars["${ch.name}.count"]!!
        fExprs += Eq(cnt.ref, iLit(0))
      }
    }

    initFormula = SmartBoolExprs.And(fExprs)
  }

  private fun initVarOrArray(
    decl: DveVarOrArrayDecl,
    processName: String?,
    fExprs: MutableList<Expr<BoolType>>,
  ) {
    when (decl) {
      is DveVarOrArrayDecl.Scalar -> {
        if (decl.decl.isConst) return
        val v = varMap[varKey(processName, decl.decl.name)]!!
        val init = decl.decl.initialValue?.let { translateExpr(it, null) } ?: iLit(0)
        fExprs += Eq(v.ref, init)
      }
      is DveVarOrArrayDecl.Array -> {
        if (decl.decl.isConst) return
        for (i in 0 until decl.decl.size) {
          val v = varMap[varKey(processName, decl.decl.name, i)]!!
          val init =
            decl.decl.initialValues?.getOrNull(i)?.let { translateExpr(it, null) } ?: iLit(0)
          fExprs += Eq(v.ref, init)
        }
      }
    }
  }

  private fun buildTrans() {
    val branches = mutableListOf<Stmt>()
    val anyCommitted = buildAnyCommittedExpr()

    val sendMap = mutableMapOf<String, MutableList<Pair<DveProcess, DveTransition>>>()
    val recvMap = mutableMapOf<String, MutableList<Pair<DveProcess, DveTransition>>>()

    for (proc in model.processes) {
      for (trans in proc.transitions) {
        when (val sync = trans.sync) {
          is DveSyncAction.Send ->
            sendMap.getOrPut(sync.channelName) { mutableListOf() } += proc to trans
          is DveSyncAction.Receive ->
            recvMap.getOrPut(sync.channelName) { mutableListOf() } += proc to trans
          null -> branches += buildLocalTransBranch(proc, trans, anyCommitted)
        }
      }
    }

    for (ch in model.channels) {
      if (ch.bufferSize == 0) {
        val sends = sendMap[ch.name] ?: continue
        val recvs = recvMap[ch.name] ?: continue
        for ((sProc, sTrans) in sends) for ((rProc, rTrans) in recvs) {
          if (sProc.name == rProc.name) continue
          branches += buildRendezvousBranch(sProc, sTrans, rProc, rTrans, anyCommitted)
        }
      } else {
        for ((sProc, sTrans) in (sendMap[ch.name] ?: emptyList())) branches +=
          buildBufferedSendBranch(ch, sProc, sTrans, anyCommitted)
        for ((rProc, rTrans) in (recvMap[ch.name] ?: emptyList())) branches +=
          buildBufferedRecvBranch(ch, rProc, rTrans, anyCommitted)
      }
    }

    tranStmt = NonDetStmt.of(branches.ifEmpty { listOf(SequenceStmt.of(listOf())) })
  }

  private fun buildAnyCommittedExpr(): Expr<BoolType>? {
    val terms = mutableListOf<Expr<BoolType>>()
    for (proc in model.processes) {
      val pc = pcVars[proc.name]!!
      for (state in proc.committedStates) terms += Eq(pc.ref, stateLit(proc.name, state))
    }
    return if (terms.isEmpty()) null else SmartBoolExprs.Or(terms)
  }

  private fun buildLocalTransBranch(
    proc: DveProcess,
    trans: DveTransition,
    anyCommitted: Expr<BoolType>?,
  ): Stmt {
    val pc = pcVars[proc.name]!!
    require(trans.sourceState in proc.states && trans.targetState in proc.states) {
      "Transition in process '${proc.name}' references unknown state(s): '${trans.sourceState}' -> '${trans.targetState}'"
    }

    var guard: Expr<BoolType> = Eq(pc.ref, stateLit(proc.name, trans.sourceState))
    if (trans.guard != null)
      guard = SmartBoolExprs.And(guard, dveExprToBool(trans.guard, proc.name))
    if (trans.sourceState !in proc.committedStates && anyCommitted != null)
      guard = SmartBoolExprs.And(guard, SmartBoolExprs.Not(anyCommitted))

    val stmts = mutableListOf<Stmt>()
    stmts += AssumeStmt.of(guard)
    stmts += AssignStmt.of(pc, stateLit(proc.name, trans.targetState))
    for (effect in trans.effects) stmts += buildAssignment(effect, proc.name)
    return SequenceStmt.of(stmts)
  }

  private fun buildRendezvousBranch(
    sProc: DveProcess,
    sTrans: DveTransition,
    rProc: DveProcess,
    rTrans: DveTransition,
    anyCommitted: Expr<BoolType>?,
  ): Stmt {
    val sSend = sTrans.sync as DveSyncAction.Send
    val rRecv = rTrans.sync as DveSyncAction.Receive
    val sPC = pcVars[sProc.name]!!
    val rPC = pcVars[rProc.name]!!
    require(sTrans.sourceState in sProc.states && sTrans.targetState in sProc.states) {
      "Transition in process '${sProc.name}' references unknown state(s): '${sTrans.sourceState}' -> '${sTrans.targetState}'"
    }
    require(rTrans.sourceState in rProc.states && rTrans.targetState in rProc.states) {
      "Transition in process '${rProc.name}' references unknown state(s): '${rTrans.sourceState}' -> '${rTrans.targetState}'"
    }

    var guard: Expr<BoolType> =
      SmartBoolExprs.And(
        Eq(sPC.ref, stateLit(sProc.name, sTrans.sourceState)),
        Eq(rPC.ref, stateLit(rProc.name, rTrans.sourceState)),
      )
    if (sTrans.guard != null)
      guard = SmartBoolExprs.And(guard, dveExprToBool(sTrans.guard, sProc.name))
    if (rTrans.guard != null)
      guard = SmartBoolExprs.And(guard, dveExprToBool(rTrans.guard, rProc.name))
    val sSrcCommitted = sTrans.sourceState in sProc.committedStates
    val rSrcCommitted = rTrans.sourceState in rProc.committedStates
    if (!sSrcCommitted && !rSrcCommitted && anyCommitted != null)
      guard = SmartBoolExprs.And(guard, SmartBoolExprs.Not(anyCommitted))

    val stmts = mutableListOf<Stmt>()
    stmts += AssumeStmt.of(guard)

    // Capture send values in temps before any writes
    val tmpVars =
      sSend.values.mapIndexed { i, valExpr ->
        Decls.Var("__dve_sync_tmp_${sSend.channelName}_$i", IntType.getInstance()).also { tmp ->
          stmts += AssignStmt.of(tmp, translateExpr(valExpr, sProc.name) as Expr<IntType>)
        }
      }

    stmts += AssignStmt.of(sPC, stateLit(sProc.name, sTrans.targetState))
    for (effect in sTrans.effects) stmts += buildAssignment(effect, sProc.name)
    for ((i, lval) in rRecv.variables.withIndex()) if (i < tmpVars.size)
      stmts += buildLvalueAssignment(lval, tmpVars[i].ref, rProc.name)
    stmts += AssignStmt.of(rPC, stateLit(rProc.name, rTrans.targetState))
    for (effect in rTrans.effects) stmts += buildAssignment(effect, rProc.name)
    return SequenceStmt.of(stmts)
  }

  private fun buildBufferedSendBranch(
    ch: DveChannelDecl,
    proc: DveProcess,
    trans: DveTransition,
    anyCommitted: Expr<BoolType>?,
  ): Stmt {
    val send = trans.sync as DveSyncAction.Send
    val pc = pcVars[proc.name]!!
    val countVar = chanVars["${ch.name}.count"]!!
    require(trans.sourceState in proc.states && trans.targetState in proc.states) {
      "Transition in process '${proc.name}' references unknown state(s): '${trans.sourceState}' -> '${trans.targetState}'"
    }

    var guard: Expr<BoolType> =
      SmartBoolExprs.And(
        Eq(pc.ref, stateLit(proc.name, trans.sourceState)),
        Lt(countVar.ref, iLit(ch.bufferSize)),
      )
    if (trans.guard != null)
      guard = SmartBoolExprs.And(guard, dveExprToBool(trans.guard, proc.name))
    if (trans.sourceState !in proc.committedStates && anyCommitted != null)
      guard = SmartBoolExprs.And(guard, SmartBoolExprs.Not(anyCommitted))

    val stmts = mutableListOf<Stmt>()
    stmts += AssumeStmt.of(guard)
    for ((i, valExpr) in send.values.withIndex()) {
      val v = translateExpr(valExpr, proc.name)
      for (slot in 0 until ch.bufferSize) {
        val sv =
          chanVars["${ch.name}.slot${slot}.field${i}"]
            ?: Decls.Var("${ch.name}_slot${slot}_field$i", IntType.getInstance()).also { sv ->
              chanVars["${ch.name}.slot${slot}.field$i"] = sv
            }
        stmts += buildConditionalAssign(Eq(countVar.ref, iLit(slot)), sv, v)
      }
    }
    stmts += AssignStmt.of(countVar, Add(countVar.ref, iLit(1)) as Expr<IntType>)
    stmts += AssignStmt.of(pc, stateLit(proc.name, trans.targetState))
    for (effect in trans.effects) stmts += buildAssignment(effect, proc.name)
    return SequenceStmt.of(stmts)
  }

  private fun buildBufferedRecvBranch(
    ch: DveChannelDecl,
    proc: DveProcess,
    trans: DveTransition,
    anyCommitted: Expr<BoolType>?,
  ): Stmt {
    val recv = trans.sync as DveSyncAction.Receive
    val pc = pcVars[proc.name]!!
    val countVar = chanVars["${ch.name}.count"]!!
    require(trans.sourceState in proc.states && trans.targetState in proc.states) {
      "Transition in process '${proc.name}' references unknown state(s): '${trans.sourceState}' -> '${trans.targetState}'"
    }

    var guard: Expr<BoolType> =
      SmartBoolExprs.And(
        Eq(pc.ref, stateLit(proc.name, trans.sourceState)),
        Gt(countVar.ref, iLit(0)),
      )
    if (trans.guard != null)
      guard = SmartBoolExprs.And(guard, dveExprToBool(trans.guard, proc.name))
    if (trans.sourceState !in proc.committedStates && anyCommitted != null)
      guard = SmartBoolExprs.And(guard, SmartBoolExprs.Not(anyCommitted))

    val stmts = mutableListOf<Stmt>()
    stmts += AssumeStmt.of(guard)
    for ((i, lval) in recv.variables.withIndex()) {
      val slot0Var =
        chanVars["${ch.name}.slot0.field$i"]
          ?: Decls.Var("${ch.name}_slot0_field$i", IntType.getInstance()).also { sv ->
            chanVars["${ch.name}.slot0.field$i"] = sv
          }
      stmts += buildLvalueAssignment(lval, slot0Var.ref, proc.name)
    }
    // Shift FIFO buffer left
    if (ch.typedFields.isNotEmpty()) {
      for (slot in 0 until ch.bufferSize - 1) for (field in ch.typedFields.indices) {
        val sv =
          chanVars["${ch.name}.slot${slot}.field$field"]
            ?: Decls.Var("${ch.name}_slot${slot}_field$field", IntType.getInstance())
        val svNext =
          chanVars["${ch.name}.slot${slot + 1}.field$field"]
            ?: Decls.Var("${ch.name}_slot${slot + 1}_field$field", IntType.getInstance())
        stmts += AssignStmt.of(sv, svNext.ref)
      }
    }
    stmts += AssignStmt.of(countVar, Sub(countVar.ref, iLit(1)) as Expr<IntType>)
    stmts += AssignStmt.of(pc, stateLit(proc.name, trans.targetState))
    for (effect in trans.effects) stmts += buildAssignment(effect, proc.name)
    return SequenceStmt.of(stmts)
  }

  private fun buildConditionalAssign(cond: Expr<BoolType>, lhs: VarDecl<*>, rhs: Expr<*>): Stmt =
    IfStmt.of(cond, AssignStmt.create<IntType>(lhs, rhs as Expr<IntType>))

  fun buildProp(propType: DveToXsts.PropType): Expr<BoolType> {
    if (propType == DveToXsts.PropType.FULL_EXPLORATION) return True()
    val terms = mutableListOf<Expr<BoolType>>()
    for (proc in model.processes) {
      val pc = pcVars[proc.name]!!
      for (assertion in proc.assertions) {
        if (assertion.stateName !in proc.states) continue
        val expr = dveExprToBool(assertion.expression, proc.name)
        terms +=
          BoolExprs.Not(
            BoolExprs.And(Eq(pc.ref, stateLit(proc.name, assertion.stateName)), BoolExprs.Not(expr))
          )
      }
    }
    return if (terms.isEmpty()) True() else SmartBoolExprs.And(terms)
  }

  private fun buildAssignment(effect: DveAssignment, ctx: String): Stmt =
    buildLvalueAssignment(effect.lvalue, translateExpr(effect.rvalue, ctx), ctx)

  private fun buildLvalueAssignment(lval: DveLValue, rhs: Expr<*>, ctx: String): Stmt =
    when (lval) {
      is DveLValue.VarLValue -> {
        val procCtx = lval.processName ?: ctx
        val v =
          lookupVar(procCtx, lval.varName)
            ?: throw IllegalArgumentException(
              "Unknown variable: ${lval.processName}.${lval.varName}"
            )
        AssignStmt.of(v, rhs as Expr<IntType>)
      }
      is DveLValue.ArrayLValue -> {
        val procCtx = lval.processName ?: ctx
        buildArrayAssignment(procCtx, lval.varName, translateExpr(lval.index, ctx), rhs)
      }
    }

  private fun buildArrayAssignment(
    procCtx: String,
    arrName: String,
    idxExpr: Expr<*>,
    rhs: Expr<*>,
  ): Stmt {
    val slots = findArraySlots(procCtx, arrName)
    if (slots.isEmpty()) throw IllegalArgumentException("Unknown array: $procCtx.$arrName")
    if (idxExpr is IntLitExpr) {
      val i = idxExpr.value.toInt()
      val slot = if (i in slots.indices) slots[i] else slots.last()
      return AssignStmt.of(slot, rhs as Expr<IntType>)
    }
    return SequenceStmt.of(
      slots.mapIndexed { i, slot -> buildConditionalAssign(Eq(idxExpr, iLit(i)), slot, rhs) }
    )
  }

  fun translateExpr(expr: DveExpression, contextProcess: String?): Expr<*> =
    when (expr) {
      is DveExpression.LiteralExpr -> iLit(expr.value)
      is DveExpression.VarRefExpr -> {
        val procCtx = expr.processName ?: contextProcess
        val constVal =
          constScalars[varKey(procCtx, expr.varName)] ?: constScalars[varKey(null, expr.varName)]
        if (constVal != null) iLit(constVal)
        else
          lookupVar(procCtx, expr.varName)?.ref
            ?: throw IllegalArgumentException(
              "Undeclared variable: ${expr.processName}.${expr.varName}"
            )
      }
      is DveExpression.ArrayAccessExpr -> {
        val procCtx = expr.processName ?: contextProcess
        buildArrayRead(procCtx, expr.varName, translateExpr(expr.index, contextProcess))
      }
      is DveExpression.ProcessStateExpr ->
        throw UnsupportedOperationException(
          "ProcessStateExpr in integer arithmetic context is not supported."
        )
      is DveExpression.UnaryExpr ->
        when (expr.op) {
          DveUnaryOp.NEG -> Neg(translateExpr(expr.operand, contextProcess))
          DveUnaryOp.NOT ->
            throw UnsupportedOperationException(
              "Unary NOT in pure integer context is not supported."
            )
          DveUnaryOp.BITNOT ->
            throw UnsupportedOperationException("Bitwise NOT (~) is not supported.")
        }
      is DveExpression.BinaryExpr -> translateBinaryIntExpr(expr, contextProcess)
    }

  private fun translateBinaryIntExpr(
    expr: DveExpression.BinaryExpr,
    contextProcess: String?,
  ): Expr<*> =
    when (expr.op) {
      DveBinaryOp.ADD ->
        Add(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.SUB ->
        Sub(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.MUL ->
        Mul(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.DIV ->
        Div(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.MOD ->
        Mod(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      // Boolean-valued operators used in arithmetic context (C semantics: yields 0 or 1)
      DveBinaryOp.LT,
      DveBinaryOp.LEQ,
      DveBinaryOp.GT,
      DveBinaryOp.GEQ,
      DveBinaryOp.EQ,
      DveBinaryOp.NEQ,
      DveBinaryOp.AND,
      DveBinaryOp.OR -> Exprs.Ite(translateBinaryBoolExpr(expr, contextProcess), iLit(1), iLit(0))
      else -> throw UnsupportedOperationException("Operator ${expr.op} used in integer context.")
    }

  fun dveExprToBool(expr: DveExpression, contextProcess: String?): Expr<BoolType> =
    when (expr) {
      is DveExpression.LiteralExpr -> if (expr.value != 0) BoolExprs.True() else BoolExprs.False()
      is DveExpression.VarRefExpr -> Neq(translateExpr(expr, contextProcess), iLit(0))
      is DveExpression.ArrayAccessExpr -> Neq(translateExpr(expr, contextProcess), iLit(0))
      is DveExpression.ProcessStateExpr -> {
        val pc =
          pcVars[expr.processName]
            ?: throw IllegalArgumentException("Unknown process: ${expr.processName}")
        if (
          expr.stateName !in
            (model.processes.find { it.name == expr.processName }?.states ?: emptyList())
        )
          throw IllegalArgumentException("Unknown state: ${expr.processName}.${expr.stateName}")
        Eq(pc.ref, stateLit(expr.processName, expr.stateName))
      }
      is DveExpression.UnaryExpr ->
        when (expr.op) {
          DveUnaryOp.NOT -> SmartBoolExprs.Not(dveExprToBool(expr.operand, contextProcess))
          DveUnaryOp.NEG -> Neq(translateExpr(expr, contextProcess), iLit(0))
          DveUnaryOp.BITNOT ->
            throw UnsupportedOperationException("Bitwise NOT (~) is not supported.")
        }
      is DveExpression.BinaryExpr -> translateBinaryBoolExpr(expr, contextProcess)
    }

  private fun translateBinaryBoolExpr(
    expr: DveExpression.BinaryExpr,
    contextProcess: String?,
  ): Expr<BoolType> =
    when (expr.op) {
      DveBinaryOp.AND ->
        SmartBoolExprs.And(
          dveExprToBool(expr.left, contextProcess),
          dveExprToBool(expr.right, contextProcess),
        )
      DveBinaryOp.OR ->
        SmartBoolExprs.Or(
          dveExprToBool(expr.left, contextProcess),
          dveExprToBool(expr.right, contextProcess),
        )
      DveBinaryOp.EQ ->
        Eq(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.NEQ ->
        Neq(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.LT ->
        Lt(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.LEQ ->
        Leq(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.GT ->
        Gt(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.GEQ ->
        Geq(translateExpr(expr.left, contextProcess), translateExpr(expr.right, contextProcess))
      DveBinaryOp.ADD,
      DveBinaryOp.SUB,
      DveBinaryOp.MUL,
      DveBinaryOp.DIV,
      DveBinaryOp.MOD -> Neq(translateBinaryIntExpr(expr, contextProcess), iLit(0))
      DveBinaryOp.BITAND,
      DveBinaryOp.BITOR,
      DveBinaryOp.BITXOR,
      DveBinaryOp.SHL,
      DveBinaryOp.SHR ->
        throw UnsupportedOperationException("Bitwise operator ${expr.op} is not supported.")
    }

  private fun buildArrayRead(procCtx: String?, arrName: String, idxExpr: Expr<*>): Expr<IntType> {
    val slots = findArraySlots(procCtx, arrName)
    if (slots.isEmpty()) throw IllegalArgumentException("Unknown array: $procCtx.$arrName")
    if (idxExpr is IntLitExpr) {
      val i = idxExpr.value.toInt()
      return if (i in slots.indices) slots[i].ref else slots.last().ref
    }
    var result: Expr<IntType> = slots.last().ref
    for (i in slots.size - 2 downTo 0) result =
      Exprs.Ite(Eq(idxExpr, iLit(i)), slots[i].ref, result)
    return result
  }

  // =========================================================================
  // Helpers
  // =========================================================================

  private fun findArraySlots(procCtx: String?, arrName: String): List<VarDecl<IntType>> =
    (0 until MAX_ARRAY_SLOTS).mapNotNull { i ->
      varMap[varKey(procCtx, arrName, i)] ?: varMap[varKey(null, arrName, i)]
    }

  private fun lookupVar(procCtx: String?, varName: String): VarDecl<IntType>? =
    varMap[varKey(procCtx, varName)] ?: varMap[varKey(null, varName)]

  private fun stateLit(processName: String, stateName: String): EnumLitExpr =
    EnumLitExpr.of(pcVars[processName]!!.type, stateName)

  companion object {
    private const val MAX_ARRAY_SLOTS = 256

    fun varKey(processName: String?, varName: String, index: Int? = null): String {
      val base = if (processName != null) "${processName}__${varName}" else varName
      return if (index != null) "${base}__$index" else base
    }

    fun varXstsName(processName: String?, varName: String, index: Int? = null): String {
      val base = if (processName != null) "${processName}_${varName}" else varName
      return if (index != null) "${base}_$index" else base
    }

    fun iLit(value: Int): hu.bme.mit.theta.core.type.inttype.IntLitExpr = IntExprs.Int(value)
  }
}
