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
    |    contains Address address
    |    contains MemoryObject[] parts
    |}
    |
    |class Address {
    |    int address
    |}
    |
    |abstract class Pointable.
    |
    |class InvalidMemory extends Pointable.
    |
    |abstract class MemoryObject extends Pointable {
    |    int offset
    |}
    |
    |class Value extends MemoryObject {
    |    int value
    |}
    |
    |abstract class AbstractPointer {
    |    Pointable target
    |}
    |
    |class Pointer extends AbstractPointer, MemoryObject.
    |
    |class NullPointer extends AbstractPointer.
    |
    |class NamedPointer {
    |    string name
    |    contains Pointer pointer
    |}
    """
      .trimMargin()

  protected val regionExists: String =
    """
    |pred regionExists(MemoryRegion region, Address address) <->
    |    exists(region), MemoryRegion::address(region, address).
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

  protected val invalidMemorySetup: String
    get() =
      """
      |InvalidMemory(null).
      |scope InvalidMemory = 1.
      |atom null.
      |
      |NullPointer(nullptr).
      |scope NullPointer = 1.
      |atom nullptr.
      |offset(nullptr): 0.
      |target(nullptr, null).
      """
        .trimMargin()

  protected abstract val transitionDeclarations: List<String>

  protected val transitions: String
    get() = transitionDeclarations.joinToString("\n\n")

  protected val topLevelDeclaration: List<String>
    get() = listOf(metamodel, regionExists, environmentSetup, invalidMemorySetup, transitions)

  protected val Type.refineryType: String
    get() =
      when (this) {
        is BoolType -> "boolean"
        is IntType -> "int"
        else -> error("Unsupported type in RefineryTransformationSystemBuilder: $this")
      }

  open fun build(): String = topLevelDeclaration.joinToString("\n\n")
}
