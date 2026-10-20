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

import hu.bme.mit.theta.core.serialization.StmtReferenceSerializer
import kotlinx.serialization.Serializable

/**
 * A statement. The hierarchy is sealed: statements defined outside this package extend
 * [ForeignStmt].
 */
@Serializable(with = StmtReferenceSerializer::class)
sealed interface Stmt {
  fun <P, R> accept(visitor: StmtVisitor<in P, out R>, param: P): R
}

/**
 * The extension point of the sealed [Stmt] hierarchy, for statements defined outside of it (e.g.
 * frontend-internal placeholders). Code switching over [Stmt] handles all of them with one branch.
 */
abstract class ForeignStmt : Stmt
