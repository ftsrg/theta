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

/** Factory class to create declarations. */
@Suppress("FunctionName")
object Decls {
  /** Create a constant declaration with a given name and type. */
  @JvmStatic fun <T : Type> Const(name: String, type: T): ConstDecl<T> = BasicConstDecl(name, type)

  /** Create a parameter declaration with a given name and type. */
  @JvmStatic fun <T : Type> Param(name: String, type: T): ParamDecl<T> = ParamDecl(name, type)

  /** Create a variable declaration with a given type. */
  @JvmStatic fun <T : Type> Var(name: String, type: T): VarDecl<T> = VarDecl(name, type)
}
