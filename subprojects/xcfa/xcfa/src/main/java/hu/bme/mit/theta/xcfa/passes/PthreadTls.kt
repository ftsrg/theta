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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq
import hu.bme.mit.theta.core.type.anytype.Dereference
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.type.anytype.Reference
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Read
import hu.bme.mit.theta.core.type.arraytype.ArrayExprs.Write
import hu.bme.mit.theta.core.type.arraytype.ArrayType
import hu.bme.mit.theta.core.type.booltype.BoolExprs.True
import hu.bme.mit.theta.core.utils.ExprUtils
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.AssignStmtLabel
import hu.bme.mit.theta.xcfa.utils.defaultValue
import hu.bme.mit.theta.xcfa.utils.integerOf
import java.util.WeakHashMap

private val THREAD_SPECIFIC_MODELS = WeakHashMap<XcfaBuilder, ThreadSpecificModel>()

/**
 * Lower calls before reference elimination; ThreadLocalVarPass later gives each thread its slots.
 */
internal fun modelThreadSpecificCall(
  builder: XcfaProcedureBuilder,
  call: InvokeLabel,
  parseContext: ParseContext,
): List<XcfaLabel> {
  val model =
    synchronized(THREAD_SPECIFIC_MODELS) {
      THREAD_SPECIFIC_MODELS.getOrPut(builder.parent) {
        ThreadSpecificModel(builder.parent, parseContext)
      }
    }
  return model.lower(call, parseContext)
}

private class ThreadSpecificModel(xcfa: XcfaBuilder, parseContext: ParseContext) {
  private val keyType = CComplexType.getUnsignedInt(parseContext).smtType as Type
  private val pointerType = CComplexType.getUnsignedLong(parseContext).smtType as Type
  private val nextKey = Var("__theta_next_tls_key", keyType)
  private val slots = Var("__theta_tls_slots", ArrayType.of(keyType, pointerType))

  init {
    xcfa.addVar(XcfaGlobalVar(nextKey, keyType.defaultValue, atomic = true))
    xcfa.addVar(XcfaGlobalVar(slots, slots.type.defaultValue, threadLocal = true))
  }

  fun lower(call: InvokeLabel, parseContext: ParseContext): List<XcfaLabel> {
    val ret = call.params[0]
    fun assign(target: Expr<*>, value: Expr<*>) = AssignStmtLabel(target, value, call.metadata)
    fun success() = assign(ret, ret.type.integerOf(0))

    return when (call.name) {
      "pthread_key_create" -> {
        val destructor = call.params[2]
        check(ExprUtils.simplify(Eq(destructor, destructor.type.integerOf(0))) == True()) {
          "pthread_key_create with non-null destructor is not supported"
        }
        val ptr = call.params[1]
        val key =
          if (ptr is Reference<*, *> && ptr.expr is RefExpr<*>) ptr.expr
          else {
            val pointee =
              (CComplexType.getType(ptr, parseContext) as? CPointer)?.embeddedType
                ?: error("pthread_key_create on a non-pointer argument: $ptr")
            Dereference.of(ptr, ptr.type.integerOf(0), pointee.smtType)
          }
        listOf(
          assign(nextKey.ref, Add(nextKey.ref, keyType.integerOf(1))),
          assign(key, cast(nextKey.ref, key.type)),
          success(),
        )
      }
      "pthread_getspecific" ->
        listOf(assign(ret, cast(Read(slots.ref, cast(call.params[1], keyType)), ret.type)))
      "pthread_setspecific" ->
        listOf(
          assign(
            slots.ref,
            Write(slots.ref, cast(call.params[1], keyType), cast(call.params[2], pointerType)),
          ),
          success(),
        )
      else -> error("Unsupported thread-specific call ${call.name}")
    }
  }
}
