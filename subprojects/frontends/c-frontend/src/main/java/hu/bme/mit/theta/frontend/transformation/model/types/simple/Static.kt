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

/**
 * The `static` storage-class specifier. Only meaningful on a *local* declaration, where it gives
 * the object static storage duration -- initialised once, surviving across calls -- which
 * `FunctionVisitor` implements by promoting the declaration to a global. At file scope the object
 * is already a global and the specifier only limits linkage, which the model does not represent, so
 * it is recorded and ignored there.
 */
class Static private constructor() : CSimpleType() {

  override fun copyOf(): CSimpleType = Static().also { setUpCopy(it) }

  override fun patch(cSimpleType: CSimpleType): CSimpleType {
    cSimpleType.isStaticStorage = true
    return cSimpleType
  }

  companion object {
    @JvmField val instance = Static()
  }
}
