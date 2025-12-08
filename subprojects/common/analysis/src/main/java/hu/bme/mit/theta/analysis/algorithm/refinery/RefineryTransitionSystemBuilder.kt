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
package hu.bme.mit.theta.analysis.algorithm.refinery

import hu.bme.mit.theta.core.decl.Decl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.booltype.BoolType
import hu.bme.mit.theta.core.type.inttype.IntType

abstract class RefineryTransitionSystemBuilder {

  companion object {

    const val ENVIRONMENT = "env"
  }

  protected val variables = mutableSetOf<Decl<*>>()

  protected val metamodel: String =
    """
    |class MemoryRegion {
    |    contains Value address
    |    contains MemoryObject[] parts
    |}
    |
    |class MemoryObject {
    |    int offset
    |    contains Pointable object
    |}
    |
    |abstract class Pointable.
    |
    |class Pointer extends Pointable {
    |    contains MemoryObject target
    |}
    |
    |class NamedPointer extends Pointer {
    |    string name
    |}
    |
    |class Value extends Pointable {
    |    int value
    |}
    """
      .trimMargin()

  protected open val environmentDeclarations: List<String>
    get() =
      listOf("contains NamedPointer[] pointers") +
        variables.map { "${it.type.refineryType} ${it.name}" }

  protected val environmentSetup: String
    get() =
      """
    |class Environment {
    |    ${environmentDeclarations.joinToString("\n    ")}
    |}
    |
    |scope Environment = 1.
    |
    |Environment($ENVIRONMENT).
    |atom $ENVIRONMENT.
    """
        .trimMargin()

  protected val regionExists: String =
    """
    |pred regionExists(MemoryRegion region, Value address) <->
    |    exists(region), address(region, address).
    """
      .trimMargin()

  protected abstract val transitionDeclarations: List<String>

  protected val transitions: String
    get() = transitionDeclarations.joinToString("\n\n")

  protected val topLevelDeclaration: List<String>
    get() = listOf(metamodel, regionExists, environmentSetup, transitions)

  protected val Type.refineryType: String
    get() =
      when (this) {
        is BoolType -> "boolean"
        is IntType -> "int"
        else -> error("Unsupported type in RefineryTransformationSystemBuilder: $this")
      }

  open fun build(): String = topLevelDeclaration.joinToString("\n\n")
}
