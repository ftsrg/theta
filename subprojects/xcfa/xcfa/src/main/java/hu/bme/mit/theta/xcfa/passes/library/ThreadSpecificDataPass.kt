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
package hu.bme.mit.theta.xcfa.passes.library

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.Assume
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.Exprs.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.booltype.BoolExprs.And
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.splitIf
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.HavocStmtLabel
import hu.bme.mit.theta.xcfa.utils.asConstantBigInteger
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Models thread-specific data. The value of each key is a thread-local variable (split per thread
 * by [hu.bme.mit.theta.xcfa.passes.concurrency.ThreadLocalVarPass]), and `pthread_getspecific` and
 * `pthread_setspecific` choose it by the key, which holds the number of its `pthread_key_create`. A
 * key with no matching create is an invalid one, whose result is left unconstrained.
 *
 * A thread routine that returns runs the destructor of a key whose value is not NULL, after setting
 * the value to NULL, at most [DESTRUCTOR_ITERATIONS] times. The process exit that a return from
 * `main` makes runs none. Everything outside this model is refused: a create that may run more than
 * once, more than one key with a destructor (they run in an unspecified order), and a destructor
 * together with `pthread_exit`, which leaves before the routine returns.
 */
class ThreadSpecificDataPass(private val parseContext: ParseContext) : ProcedurePass {

  companion object {
    /** glibc's `PTHREAD_DESTRUCTOR_ITERATIONS`. */
    const val DESTRUCTOR_ITERATIONS = 4

    private val FUNCTIONS =
      setOf("pthread_key_create", "pthread_getspecific", "pthread_setspecific")
  }

  private fun isCall(label: XcfaLabel, names: Set<String>, builder: XcfaProcedureBuilder) =
    label is InvokeLabel &&
      label.name in names &&
      builder.parent.getProcedures().none { it.name == label.name }

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val procedures = builder.parent.getProcedures()
    val used =
      procedures.any { p ->
        p.getEdges().any { e -> e.getFlatLabels().any { isCall(it, FUNCTIONS, builder) } }
      }
    if (!used) return builder
    val keys = keys(builder)

    for (edge in ArrayList(builder.getEdges())) {
      if (edge.getFlatLabels().none { isCall(it, FUNCTIONS, builder) }) continue
      val parts = edge.splitIf { isCall(it, FUNCTIONS, builder) }
      builder.removeEdge(edge)
      for (part in parts) {
        val label = part.getFlatLabels().singleOrNull()
        if (label == null || !isCall(label, FUNCTIONS, builder)) {
          builder.addEdge(part)
          continue
        }
        branches(label as InvokeLabel, keys).forEach {
          builder.addEdge(XcfaEdge(part.source, part.target, SequenceLabel(it), part.metadata))
        }
      }
    }

    if (isThreadRoutine(builder)) addDestructors(builder, keys)
    return builder
  }

  /**
   * The keys, numbered in the order of their creates, which may only be in the entry procedure.
   * Every procedure has its own instance of this pass, so they are kept in the model.
   */
  private fun keys(builder: XcfaProcedureBuilder): List<ThreadSpecificKey> =
    builder.parent.threadSpecificKeys
      ?: findKeys(builder).also { builder.parent.threadSpecificKeys = it }

  private fun findKeys(builder: XcfaProcedureBuilder): List<ThreadSpecificKey> {
    val procedures = builder.parent.getProcedures()
    val entry = builder.parent.getInitProcedures().map { it.first }
    val creates =
      procedures.flatMap { p ->
        p.getEdges().flatMap { e ->
          e.getFlatLabels()
            .filter { isCall(it, setOf("pthread_key_create"), builder) }
            .map { Triple(p, e, it as InvokeLabel) }
        }
      }
    creates.forEach { (p, e, _) ->
      if (p !in entry || e.source.onCycle() || p.calledFrom(builder)) {
        throw UnsupportedFrontendElementException(
          "pthread_key_create that may run more than once (in ${p.name})"
        )
      }
    }
    val pointer = CPointer(null, CVoid(null, parseContext), parseContext)
    val keys =
      creates.mapIndexed { i, (_, _, call) ->
        val name = "__theta_tls_slot_${i + 1}"
        val slot =
          builder.parent.getVars().find { it.wrappedVar.name == name }?.wrappedVar
            ?: Decls.Var(name, pointer.smtType).also {
              parseContext.metadata.create(it.ref, "cType", pointer)
              builder.parent.addVar(XcfaGlobalVar(it, pointer.nullValue, threadLocal = true))
            }
        ThreadSpecificKey(i + 1, call, slot, destructor(call.params[2], builder))
      }
    if (keys.count { it.destructor != null } > 1) {
      throw UnsupportedFrontendElementException("More than one pthread key with a destructor")
    }
    val exits =
      procedures.any { p ->
        p.getEdges().any { e ->
          e.getFlatLabels().any { isCall(it, setOf("pthread_exit"), builder) }
        }
      }
    if (exits && keys.any { it.destructor != null }) {
      throw UnsupportedFrontendElementException("pthread key destructor with pthread_exit")
    }
    return keys
  }

  private fun destructor(routine: Expr<*>, builder: XcfaProcedureBuilder): XcfaProcedureBuilder? {
    if (ExprUtils.simplify(routine).asConstantBigInteger()?.signum() == 0) return null
    val designator = if (routine is Reference<*, *>) routine.expr else routine
    val name = ((designator as? RefExpr<*>)?.decl as? VarDecl<*>)?.name
    return builder.parent.getProcedures().find { it.name == name && it.getParams().size == 2 }
      ?: throw UnsupportedFrontendElementException("Unsupported pthread key destructor: $routine")
  }

  /** The alternatives replacing [call], one per key and one for an invalid key. */
  private fun branches(call: InvokeLabel, keys: List<ThreadSpecificKey>): List<List<XcfaLabel>> {
    val metadata = call.metadata
    val ret = call.params[0]
    val zero = { AssignStmtLabel(ret, CComplexType.getType(ret, parseContext).nullValue, metadata) }
    if (call.name == "pthread_key_create") {
      val key = keys.single { it.create === call }
      val target = pointee(call.params[1])
      val id = CComplexType.getType(target, parseContext).getValue("${key.id}")
      return listOf(listOf(AssignStmtLabel(target, id, metadata), zero()))
    }
    val key = call.params[1]
    val keyType = CComplexType.getType(key, parseContext)
    val isKey = { k: ThreadSpecificKey -> Eq(key, keyType.getValue("${k.id}")) }
    val chosen =
      keys.map { k ->
        val access =
          if (call.name == "pthread_getspecific")
            listOf(AssignStmtLabel(ret, CComplexType.getType(ret, parseContext).castTo(k.slot.ref)))
          else
            listOf(
              AssignStmtLabel(
                k.slot,
                CComplexType.getType(k.slot.ref, parseContext).castTo(call.params[2]),
                metadata,
              ),
              zero(),
            )
        listOf(StmtLabel(Assume(isKey(k)), metadata = metadata)) + access
      }
    val invalid =
      listOf(
        StmtLabel(
          Assume(And(keys.map { Neq(key, keyType.getValue("${it.id}")) })),
          metadata = metadata,
        ),
        HavocStmtLabel(ret, metadata),
      )
    return chosen + listOf(invalid)
  }

  private fun isThreadRoutine(builder: XcfaProcedureBuilder) =
    builder.parent.getProcedures().any { p ->
      p.getEdges().any { e ->
        e.getFlatLabels().any {
          isCall(it, setOf("pthread_create"), builder) &&
            (it as InvokeLabel).params.getOrNull(3)?.let(::nameOf) == builder.name
        }
      }
    }

  /** Runs the destructor of the key that has one before the routine's final location. */
  private fun addDestructors(builder: XcfaProcedureBuilder, keys: List<ThreadSpecificKey>) {
    val key = keys.singleOrNull { it.destructor != null } ?: return
    val destructor = key.destructor!!
    if (builder.calledFrom(builder)) {
      throw UnsupportedFrontendElementException(
        "pthread key destructor with a thread routine that is also called: ${builder.name}"
      )
    }
    val final = builder.finalLoc.orElse(null) ?: return
    val (ret, param) = destructor.getParams().map { it.first }
    val value = Decls.Var("__theta_tls_value_${key.id}", param.type)
    parseContext.metadata.create(value.ref, "cType", CComplexType.getType(param.ref, parseContext))
    builder.addVar(value)
    val result = Decls.Var("__theta_tls_dtor_ret_${key.id}", ret.type).also(builder::addVar)
    val slotType = CComplexType.getType(key.slot.ref, parseContext)
    val locs =
      (0..DESTRUCTOR_ITERATIONS).map {
        XcfaLocation("${builder.name}_tls_dtor_${it}_${key.id}", metadata = final.metadata)
      }
    locs.forEach(builder::addLoc)
    ArrayList(final.incomingEdges).forEach {
      builder.removeEdge(it)
      builder.addEdge(it.withTarget(locs[0]))
    }
    for (i in 0 until DESTRUCTOR_ITERATIONS) {
      val calling =
        XcfaLocation("${builder.name}_tls_dtor_call_${i}_${key.id}", metadata = final.metadata)
      builder.addLoc(calling)
      builder.addEdge(
        XcfaEdge(
          locs[i],
          calling,
          SequenceLabel(
            listOf(
              StmtLabel(Assume(Neq(key.slot.ref, slotType.nullValue))),
              AssignStmtLabel(
                value,
                CComplexType.getType(param.ref, parseContext).castTo(key.slot.ref),
              ),
              AssignStmtLabel(key.slot, slotType.nullValue),
            )
          ),
          EmptyMetaData,
        )
      )
      builder.addEdge(
        XcfaEdge(
          calling,
          locs[i + 1],
          SequenceLabel(
            listOf(InvokeLabel(destructor, listOf(result.ref, value.ref), EmptyMetaData))
          ),
          EmptyMetaData,
        )
      )
      builder.addEdge(
        XcfaEdge(
          locs[i],
          final,
          SequenceLabel(listOf(StmtLabel(Assume(Eq(key.slot.ref, slotType.nullValue))))),
          EmptyMetaData,
        )
      )
    }
    builder.addEdge(
      XcfaEdge(locs[DESTRUCTOR_ITERATIONS], final, SequenceLabel(listOf(NopLabel)), EmptyMetaData)
    )
  }

  private fun nameOf(expr: Expr<*>): String? {
    val designator = if (expr is Reference<*, *>) expr.expr else expr
    return ((designator as? RefExpr<*>)?.decl as? VarDecl<*>)?.name
  }

  /** `*ptr`: the variable itself for `&x`, otherwise a [Dereference] at offset 0. */
  private fun pointee(ptr: Expr<*>): Expr<*> {
    if (ptr is Reference<*, *> && (ptr.expr is RefExpr<*> || ptr.expr is Dereference<*, *, *>))
      return ptr.expr
    val pointee =
      (CComplexType.getType(ptr, parseContext) as? CPointer)?.embeddedType
        ?: throw UnsupportedFrontendElementException("pthread_key_create on a non-pointer: $ptr")
    val offset = CComplexType.getSignedLong(parseContext).nullValue
    return Dereference(cast(ptr, ptr.type), cast(offset, ptr.type), pointee.smtType)
  }

  private fun XcfaProcedureBuilder.calledFrom(builder: XcfaProcedureBuilder) =
    builder.parent.getProcedures().any { p ->
      p.getEdges().any { e -> e.getFlatLabels().any { it is InvokeLabel && it.name == name } }
    }

  private fun XcfaLocation.onCycle(): Boolean {
    val seen = mutableSetOf<XcfaLocation>()
    val stack = ArrayDeque(outgoingEdges.map { it.target })
    while (stack.isNotEmpty()) {
      val loc = stack.removeLast()
      if (loc == this) return true
      if (seen.add(loc)) stack.addAll(loc.outgoingEdges.map { it.target })
    }
    return false
  }
}

/** A key of [ThreadSpecificDataPass]: its number, its create, its value and its destructor. */
class ThreadSpecificKey(
  val id: Int,
  val create: InvokeLabel,
  val slot: VarDecl<*>,
  val destructor: XcfaProcedureBuilder?,
)
