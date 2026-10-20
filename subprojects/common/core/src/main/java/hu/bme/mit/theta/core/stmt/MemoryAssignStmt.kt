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
package hu.bme.mit.theta.core.stmt

import com.google.common.base.Objects
import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Dereference
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.unwrapTraceable
import kotlinx.serialization.Serializable
import kotlinx.serialization.Transient

/**
 * Assignment statement of the form *(DEREF_EXPRESSION) := EXPRESSION. The statement updates the
 * value pointed to by DEREF_EXPRESSION with the result of EXPRESSION.
 */
@Serializable
class MemoryAssignStmt<PtrType : Type, OffsetType : Type, DeclType : Type>
private constructor(
  /** The written location as given: a [Dereference], possibly wrapped with traceability info. */
  val tracedDeref: Expr<DeclType>,
  val expr: Expr<DeclType>,
) : Stmt {

  @Suppress("UNCHECKED_CAST")
  @Transient
  val deref: Dereference<PtrType, OffsetType, DeclType> =
    tracedDeref.unwrapTraceable().also {
      checkArgument(it is Dereference<*, *, *>, "Not a dereference: %s", it)
    } as Dereference<PtrType, OffsetType, DeclType>

  override fun <P, R> accept(visitor: StmtVisitor<in P, out R>, param: P): R =
    visitor.visit(this, param)

  override fun hashCode(): Int = Objects.hashCode(deref, expr)

  override fun equals(other: Any?): Boolean =
    if (this === other) true
    else if (other != null && javaClass == other.javaClass) {
      Objects.equal(deref, (other as MemoryAssignStmt<*, *, *>).deref) &&
        Objects.equal(expr, other.expr)
    } else false

  override fun toString(): String =
    Utils.lispStringBuilder(STMT_LABEL).add(deref).add(expr).toString()

  companion object {
    private const val STMT_LABEL = "memassign"

    @JvmStatic
    fun <PtrType : Type, OffsetType : Type, DeclType : Type> of(
      deref: Dereference<PtrType, OffsetType, DeclType>,
      expr: Expr<DeclType>,
    ): MemoryAssignStmt<PtrType, OffsetType, DeclType> = MemoryAssignStmt(deref, expr)

    @Suppress("UNCHECKED_CAST")
    @JvmStatic
    fun <PtrType : Type, OffsetType : Type, DeclType : Type> create(
      deref: Dereference<PtrType, OffsetType, *>,
      expr: Expr<DeclType>,
    ): MemoryAssignStmt<PtrType, OffsetType, DeclType> =
      of(deref as Dereference<PtrType, OffsetType, DeclType>, expr)

    /** An assignment to [tracedDeref]: a [Dereference], possibly wrapped with traceability info. */
    @Suppress("UNCHECKED_CAST")
    @JvmStatic
    fun <DeclType : Type> create(
      tracedDeref: Expr<*>,
      expr: Expr<DeclType>,
    ): MemoryAssignStmt<*, *, DeclType> =
      MemoryAssignStmt<Type, Type, DeclType>(tracedDeref as Expr<DeclType>, expr)
  }
}
