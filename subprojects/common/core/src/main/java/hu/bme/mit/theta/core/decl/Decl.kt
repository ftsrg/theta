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
package hu.bme.mit.theta.core.decl

import hu.bme.mit.theta.core.serialization.DeclReferenceSerializer
import hu.bme.mit.theta.core.type.RefExpr
import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.Serializable

/**
 * A named, typed declaration. Declarations are identities, not values: a declaration is equal only
 * to itself. Create them through [Decls].
 */
@Serializable(with = DeclReferenceSerializer::class)
sealed class Decl<DeclType : Type> {

  abstract val name: String

  abstract val type: DeclType

  @Suppress("LeakingThis") val ref: RefExpr<DeclType> = RefExpr.of(this)

  @Volatile private var hashCode = 0

  final override fun hashCode(): Int {
    var result = hashCode
    if (result == 0) {
      result = HASH_SEED
      result = 31 * result + name.hashCode()
      result = 31 * result + type.hashCode()
      hashCode = result
    }
    return result
  }

  final override fun equals(other: Any?): Boolean = this === other

  companion object {
    private const val HASH_SEED = 5351
  }
}
