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
package hu.bme.mit.theta.frontend.transformation.model.types.simple

import hu.bme.mit.theta.core.type.Expr
import java.util.Optional

class Enum internal constructor(val id: String, val fields: Map<String, Optional<Expr<*>>>) :
  CSimpleType() {

  override fun patch(cSimpleType: CSimpleType): CSimpleType =
    throw RuntimeException("Should not be here! Cannot patch with an enum.")

  override val baseType: CSimpleType
    get() =
      Enum(id, fields).also {
        it.isAtomic = isAtomic
        it.isExtern = isExtern
        it.isStaticStorage = isStaticStorage
        it.isTypedef = isTypedef
        it.isVolatile = isVolatile
      }

  override fun copyOf(): CSimpleType = Enum(id, LinkedHashMap(fields)).also { setUpCopy(it) }

  companion object {
    /**
     * Global registry of enumeration-constant values, keyed by enumerator name. C enumerators are
     * ordinary integer constants usable anywhere an expression is expected, but the frontend models
     * an enum as a plain `int`, so the enumerator names would otherwise be unresolvable. This
     * registry lets the expression visitor fold an enumerator reference to its integer value. Like
     * `Struct`'s type registry, entries accumulate per process; this is harmless because each input
     * file is parsed in its own process (a re-parse of the same file re-registers identical
     * values).
     */
    private val definedConstants: MutableMap<String, Long> = LinkedHashMap()

    @JvmStatic fun getConstantValue(name: String): Long? = definedConstants[name]

    @JvmStatic
    fun defineConstant(name: String, value: Long) {
      definedConstants[name] = value
    }
  }
}
