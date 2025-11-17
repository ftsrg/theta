/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.xcfa.passes

import com.google.common.base.Preconditions
import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.MemoryAssignStmt
import hu.bme.mit.theta.core.stmt.Stmts
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Ite
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Sub
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import java.util.function.BiFunction

/**
 * Transforms GCC __atomic builtins (always assuming sequentially consistent semantics) into
 * equivalent XCFA statements. The InvokeLabel is expected to encode builtin calls as follows:
 * - Unary returning value (load): (__atomic_load_n) params: [retVar, ptrVar, memOrder]
 * - Unary store (store): (__atomic_store_n) params: [ptrVar, value, memOrder] (retVar omitted)
 * - Binary RMW returning old: (__atomic_fetch_add etc.) params: [retVar, ptrVar, value, memOrder]
 * - Binary RMW returning new: (__atomic_add_fetch etc.) params: [retVar, ptrVar, value, memOrder]
 * - Exchange returning old: (__atomic_exchange_n) params: [retVar, ptrVar, value, memOrder]
 * - Compare/exchange (bool result): (__atomic_compare_exchange_n) params:
 *   [retBoolVar, ptrVar, expectedVar, desiredValue, weakFlag, successOrder, failureOrder]
 *
 * All memory order arguments are parsed but ignored (SC assumed). Weak flag ignored.
 *
 * TODO: explicit casts between types
 */
class AtomicBuiltinsToExprsPass(val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    checkNotNull(builder.metaData["deterministic"])
    for (edge in ArrayList(builder.getEdges())) {
      val newLabels: MutableList<XcfaLabel> = ArrayList()
      var changed = false
      val sequence = edge.label as? SequenceLabel ?: continue
      for (label in sequence.labels) {
        if (label is InvokeLabel && handlers.containsKey(label.name)) {
          newLabels.add(handlers[label.name]!!.apply(builder, label))
          changed = true
        } else newLabels.add(label)
      }
      if (changed) {
        builder.removeEdge(edge)
        builder.addEdge(
          XcfaEdge(edge.source, edge.target, SequenceLabel(newLabels, edge.metadata), edge.metadata)
        )
      }
    }
    return builder
  }

  private val handlers:
    MutableMap<String, BiFunction<XcfaProcedureBuilder, InvokeLabel, XcfaLabel>> =
    LinkedHashMap()

  private fun addHandler(
    names: Array<String>,
    handler: BiFunction<XcfaProcedureBuilder, InvokeLabel, XcfaLabel>,
  ) {
    names.forEach { handlers[it] = handler }
  }

  init {
    // load/store
    addHandler(arrayOf("__atomic_load_n")) { b, c -> handleLoadN(b, c) }
    addHandler(arrayOf("__atomic_store_n")) { b, c -> handleStoreN(b, c) }

    // exchange
    addHandler(arrayOf("__atomic_exchange_n")) { b, c -> handleExchangeN(b, c) }

    // add/sub fetch (return old/new variants)
    addHandler(arrayOf("__atomic_fetch_add")) { b, c -> handleFetchAdd(b, c, returnNew = false) }
    addHandler(arrayOf("__atomic_add_fetch")) { b, c -> handleFetchAdd(b, c, returnNew = true) }
    addHandler(arrayOf("__atomic_fetch_sub")) { b, c -> handleFetchSub(b, c, returnNew = false) }
    addHandler(arrayOf("__atomic_sub_fetch")) { b, c -> handleFetchSub(b, c, returnNew = true) }

    // and/or/xor (old/new variants)
    addHandler(arrayOf("__atomic_fetch_and")) { b, c ->
      handleFetchBitwise(b, c, BitwiseOp.AND, false)
    }
    addHandler(arrayOf("__atomic_and_fetch")) { b, c ->
      handleFetchBitwise(b, c, BitwiseOp.AND, true)
    }
    addHandler(arrayOf("__atomic_fetch_or")) { b, c ->
      handleFetchBitwise(b, c, BitwiseOp.OR, false)
    }
    addHandler(arrayOf("__atomic_or_fetch")) { b, c ->
      handleFetchBitwise(b, c, BitwiseOp.OR, true)
    }
    addHandler(arrayOf("__atomic_fetch_xor")) { b, c ->
      handleFetchBitwise(b, c, BitwiseOp.XOR, false)
    }
    addHandler(arrayOf("__atomic_xor_fetch")) { b, c ->
      handleFetchBitwise(b, c, BitwiseOp.XOR, true)
    }

    // compare exchange (bool result)
    addHandler(arrayOf("__atomic_compare_exchange_n")) { b, c -> handleCompareExchangeN(b, c) }
  }

  // region Handlers
  private fun handleLoadN(builder: XcfaProcedureBuilder, invoke: InvokeLabel): XcfaLabel {
    Preconditions.checkState(invoke.params.size == 3, "__atomic_load_n arity should be 3")
    val ret = invoke.params[0]
    val ptr = invoke.params[1]
    Preconditions.checkState(ret is RefExpr<*> && ptr is Reference<*, *>)
    val varRet = (ret as RefExpr<*>).decl
    val varPtr = (ptr as Reference<*, *>).expr
    val toType = CComplexType.getType(ret, parseContext)
    val assign =
      Stmts.Assign(cast(varRet as VarDecl, varRet.type), cast(toType.castTo(varPtr), varRet.type))
    return StmtLabel(assign, metadata = invoke.metadata)
  }

  private fun handleStoreN(builder: XcfaProcedureBuilder, invoke: InvokeLabel): XcfaLabel {
    Preconditions.checkState(invoke.params.size == 4, "__atomic_store_n arity should be 4")
    val ptr = invoke.params[1]
    val value = invoke.params[2]
    Preconditions.checkState(ptr is Reference<*, *>)
    val varPtr = (ptr as Reference<*, *>).expr
    val toType = CComplexType.getType(varPtr, parseContext)
    val assign =
      if (varPtr is RefExpr<*>) {
        Stmts.Assign(
          cast(varPtr.decl as VarDecl<*>, varPtr.type),
          cast(toType.castTo(value), varPtr.type),
        )
      } else if (varPtr is Dereference<*, *, *>) {
        MemoryAssignStmt.create(varPtr, toType.castTo(value))
      } else {
        error("__atomic_store_n received unknown parameter type $varPtr")
      }
    return StmtLabel(assign, metadata = invoke.metadata)
  }

  private fun handleExchangeN(builder: XcfaProcedureBuilder, invoke: InvokeLabel): XcfaLabel {
    Preconditions.checkState(invoke.params.size == 4, "__atomic_exchange_n arity should be 4")
    val ret = invoke.params[0]
    val ptr = invoke.params[1]
    val value = invoke.params[2]
    Preconditions.checkState(ret is RefExpr<*> && ptr is Reference<*, *>)
    val varRet = (ret as RefExpr<*>).decl
    val varPtr = (ptr as Reference<*, *>).expr
    // Read old value into ret
    val oldAssign = Stmts.Assign(cast(varRet as VarDecl, varRet.type), cast(varPtr, varRet.type))
    // Write new value to ptr
    val writeAssign =
      if (varPtr is RefExpr<*>) {
        Stmts.Assign(cast(varPtr.decl as VarDecl<*>, varPtr.type), cast(value, varPtr.type))
      } else if (varPtr is Dereference<*, *, *>) {
        MemoryAssignStmt.create(varPtr, value)
      } else {
        error("__atomic_exchange_n received unknown parameter type $varPtr")
      }
    return SequenceLabel(
      listOf(StmtLabel(oldAssign), StmtLabel(writeAssign)),
      metadata = invoke.metadata,
    )
  }

  private fun handleFetchAdd(
    builder: XcfaProcedureBuilder,
    invoke: InvokeLabel,
    returnNew: Boolean,
  ): XcfaLabel {
    Preconditions.checkState(
      invoke.params.size == 4,
      "__atomic_fetch_add/add_fetch arity should be 4",
    )
    val ret = invoke.params[0]
    val ptr = invoke.params[1]
    val value = invoke.params[2]
    Preconditions.checkState(ret is RefExpr<*> && ptr is Reference<*, *>)
    val varRet = (ret as RefExpr<*>).decl
    val retType = CComplexType.getType(ret, parseContext)
    val varPtr = (ptr as Reference<*, *>).expr
    val toType = CComplexType.getType(varPtr, parseContext)
    val newVal = AbstractExprs.Add(cast(varPtr, varPtr.type), cast(value, varPtr.type))
    val retExpr =
      if (returnNew) cast(retType.castTo(newVal), varRet.type)
      else cast(retType.castTo(varPtr), varRet.type)
    val retAssign = Stmts.Assign(cast(varRet as VarDecl, varRet.type), retExpr)
    val ptrAssign =
      if (varPtr is RefExpr<*>) {
        Stmts.Assign(
          cast(varPtr.decl as VarDecl<*>, varPtr.type),
          cast(toType.castTo(newVal), varPtr.type),
        )
      } else if (varPtr is Dereference<*, *, *>) {
        MemoryAssignStmt.create(varPtr, cast(toType.castTo(newVal), varPtr.type))
      } else {
        error("__atomic_fetch_add received unknown parameter type $varPtr")
      }
    return SequenceLabel(
      listOf(StmtLabel(retAssign), StmtLabel(ptrAssign)),
      metadata = invoke.metadata,
    )
  }

  private fun handleFetchSub(
    builder: XcfaProcedureBuilder,
    invoke: InvokeLabel,
    returnNew: Boolean,
  ): XcfaLabel {
    Preconditions.checkState(
      invoke.params.size == 4,
      "__atomic_fetch_sub/sub_fetch arity should be 4",
    )
    val ret = invoke.params[0]
    val ptr = invoke.params[1]
    val value = invoke.params[2]
    Preconditions.checkState(ret is RefExpr<*> && ptr is Reference<*, *>)
    val varRet = (ret as RefExpr<*>).decl
    val varPtr = (ptr as Reference<*, *>).expr
    val newVal = Sub(cast(varPtr, varPtr.type), cast(value, varPtr.type))
    val retExpr = if (returnNew) cast(newVal, varRet.type) else cast(varPtr, varRet.type)
    val retAssign = Stmts.Assign(cast(varRet as VarDecl, varRet.type), retExpr)
    val ptrAssign =
      if (varPtr is RefExpr<*>) {
        Stmts.Assign(cast(varPtr.decl as VarDecl<*>, varPtr.type), cast(newVal, varPtr.type))
      } else if (varPtr is Dereference<*, *, *>) {
        MemoryAssignStmt.create(varPtr, cast(newVal, varPtr.type))
      } else {
        error("__atomic_fetch_sub received unknown parameter type $varPtr")
      }
    return SequenceLabel(
      listOf(StmtLabel(retAssign), StmtLabel(ptrAssign)),
      metadata = invoke.metadata,
    )
  }

  // Bitwise operations: using +, -, XOR placeholders? Real bitwise requires bitvector types; here
  // we mimic with mathematical approximations or leave TODO.
  private enum class BitwiseOp {
    AND,
    OR,
    XOR,
  }

  private fun handleFetchBitwise(
    builder: XcfaProcedureBuilder,
    invoke: InvokeLabel,
    op: BitwiseOp,
    returnNew: Boolean,
  ): XcfaLabel {
    Preconditions.checkState(invoke.params.size == 4, "__atomic_fetch_* bitwise arity should be 4")
    val ret = invoke.params[0]
    val ptr = invoke.params[1]
    val value = invoke.params[2]
    Preconditions.checkState(ret is RefExpr<*> && ptr is Reference<*, *>)
    val varRet = (ret as RefExpr<*>).decl
    val varPtr = (ptr as Reference<*, *>).expr
    // Fallback: we cannot express bitwise ops on mathematical IntType; raise unsupported.
    throw UnsupportedOperationException(
      "Bitwise atomic operations not supported yet for IntType: $op"
    )
  }

  private fun handleCompareExchangeN(
    builder: XcfaProcedureBuilder,
    invoke: InvokeLabel,
  ): XcfaLabel {
    Preconditions.checkState(
      invoke.params.size == 7,
      "__atomic_compare_exchange_n arity should be 7",
    )
    val retBool = invoke.params[0]
    val ptr = invoke.params[1]
    val expected = invoke.params[2]
    val desired = invoke.params[3]
    Preconditions.checkState(
      retBool is RefExpr<*> && ptr is Reference<*, *> && expected is Reference<*, *>
    )
    val varRet = (retBool as RefExpr<*>).decl as VarDecl<BoolType>
    val varPtr = (ptr as Reference<*, *>).expr
    val varExpected = (expected as Reference<*, *>).expr

    // Snapshot current value of ptr
    val snapshot = Decls.Var("__cmpxchg_old_${builder.getVars().size}", varPtr.type)
    builder.addVar(snapshot)
    val snapAssign = Stmts.Assign(cast(snapshot, snapshot.type), cast(varPtr, snapshot.type))

    // Compare snapshot with expected
    val successCond =
      AbstractExprs.Eq(cast(snapshot.ref, snapshot.type), cast(varExpected, snapshot.type))

    // Store success boolean in return value
    val retAssign = Stmts.Assign(varRet, successCond)

    // Update ptr: ITE(success, desired, old)
    val newPtrExpr =
      Ite<Type>(successCond, cast(desired, varPtr.type), cast(snapshot.ref, varPtr.type))
    val ptrAssign =
      if (varPtr is RefExpr<*>) {
        Stmts.Assign(cast(varPtr.decl as VarDecl<*>, varPtr.type), cast(newPtrExpr, varPtr.type))
      } else if (varPtr is Dereference<*, *, *>) {
        MemoryAssignStmt.create(varPtr, cast(newPtrExpr, varPtr.type))
      } else {
        error("__atomic_compare_exchange_n received unknown ptr type $varPtr")
      }

    // Update expected: ITE(success, expected, old) - on failure, write back old value
    val newExpectedExpr =
      Ite<Type>(
        successCond,
        cast(varExpected, varExpected.type),
        cast(snapshot.ref, varExpected.type),
      )
    val expectedAssign =
      if (varExpected is RefExpr<*>) {
        Stmts.Assign(
          cast(varExpected.decl as VarDecl<*>, varExpected.type),
          cast(newExpectedExpr, varExpected.type),
        )
      } else if (varExpected is Dereference<*, *, *>) {
        MemoryAssignStmt.create(varExpected, cast(newExpectedExpr, varExpected.type))
      } else {
        error("__atomic_compare_exchange_n received unknown expected type $varExpected")
      }

    return SequenceLabel(
      listOf(
        StmtLabel(snapAssign),
        StmtLabel(retAssign),
        StmtLabel(ptrAssign),
        StmtLabel(expectedAssign),
      ),
      metadata = invoke.metadata,
    )
  }
}
