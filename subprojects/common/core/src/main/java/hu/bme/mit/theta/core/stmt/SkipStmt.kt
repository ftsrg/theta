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
package hu.bme.mit.theta.core.stmt

import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

@Serializable
@SerialName(SkipStmt.STMT_LABEL)
data object SkipStmt : Stmt {

  internal const val STMT_LABEL = "skip"

  override fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R = visitor.visit(this, param)

  @JvmStatic fun getInstance(): SkipStmt = this

  override fun toString(): String = STMT_LABEL
}
