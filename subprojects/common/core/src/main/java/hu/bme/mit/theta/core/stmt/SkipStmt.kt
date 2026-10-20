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

import kotlinx.serialization.Serializable

/** A skip statement is a placeholder that does not perform any operation. */
@Serializable
object SkipStmt : Stmt {

  override fun <P, R> accept(visitor: StmtVisitor<in P, out R>, param: P): R =
    visitor.visit(this, param)

  override fun hashCode(): Int = HASH_CODE

  override fun equals(other: Any?): Boolean =
    this === other || (other != null && javaClass == other.javaClass)

  override fun toString(): String = STMT_LABEL

  private const val HASH_CODE = 1310147
  private const val STMT_LABEL = "skip"

  @JvmStatic fun getInstance(): SkipStmt = this
}
