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

import com.google.common.base.Preconditions.checkArgument
import hu.bme.mit.theta.common.Utils
import hu.bme.mit.theta.core.type.Type

/**
 * Base class for constants. [BasicConstDecl] is a basic constant, [IndexedConstDecl] a constant
 * belonging to a variable for some index (e.g., during unfolding paths).
 */
sealed class ConstDecl<DeclType : Type>(name: String, type: DeclType) : Decl<DeclType>(name, type) {

  final override fun toString(): String =
    Utils.lispStringBuilder(DECL_LABEL).add(name).add(type).toString()

  private companion object {
    const val DECL_LABEL = "Const"
  }
}

/** A basic constant declaration that can be directly passed to the SMT solver. */
class BasicConstDecl<DeclType : Type> internal constructor(name: String, type: DeclType) :
  ConstDecl<DeclType>(name, type)

/**
 * A constant declaration that belongs to a variable ([VarDecl]) for a given index. For example,
 * when unfolding a path, each variable will have a new constant for each step of the path.
 */
class IndexedConstDecl<DeclType : Type>
internal constructor(val varDecl: VarDecl<DeclType>, val index: Int) :
  ConstDecl<DeclType>(String.format(NAME_FORMAT, varDecl.name, index), varDecl.type) {

  init {
    checkArgument(index >= 0)
  }

  private companion object {
    const val NAME_FORMAT = "_%s:%d"
  }
}
