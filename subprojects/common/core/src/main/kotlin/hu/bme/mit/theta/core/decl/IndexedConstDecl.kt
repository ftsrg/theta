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
package hu.bme.mit.theta.core.decl

import hu.bme.mit.theta.core.type.Type
import kotlinx.serialization.SerialName
import kotlinx.serialization.Serializable

/**
 * A constant declaration that belongs to a variable ([VarDecl] declaration for a given index. For
 * example, when unfolding a path, each variable will have a new constant for each step of the path.
 *
 * @param <DeclType>
 */
@Serializable
@SerialName("IndexedConstDecl")
data class IndexedConstDecl<DeclType : Type>(val varDecl: VarDecl<DeclType>, val index: Int) :
  ConstDecl<DeclType>() {
  init {
    require(index >= 0) { "Index must be non-negative" }
  }

  companion object {
    private const val NAME_FORMAT: String = "_%s:%d"
  }

  override val name: String = String.format(NAME_FORMAT, varDecl.name, index)
  override val type: DeclType = varDecl.type
}
