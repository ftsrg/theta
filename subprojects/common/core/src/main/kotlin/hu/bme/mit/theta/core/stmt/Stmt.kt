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

import kotlinx.serialization.Polymorphic

/** Base class for all statements in the Theta framework. All subclasses must be serializable. */
@Polymorphic
interface Stmt {
  /**
   * Accepts a visitor and returns the result of the visit.
   *
   * @param visitor The visitor to accept
   * @param param Additional parameter for the visitor
   * @return The result of the visit
   */
  fun <P, R> accept(visitor: StmtVisitor<P, R>, param: P): R
}
