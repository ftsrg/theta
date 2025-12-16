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

    val String.refinerified: String
      get() = replace("::", "__")
  }

  protected val variables = mutableSetOf<Decl<*>>()

  // Metamodel

  protected val metamodel: String =
    """
    |import builtin::annotations.
    |
    |#pred transition().
    |#pred goal().
    |
    |class MemoryRegion {
    |    contains Address address
    |    contains MemoryObject[] parts
    |    int size
    |    boolean valid
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
    |    int size
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

  // Environment

  protected open val environmentDeclarations: List<String>
    get() =
      listOf("int next_address", "contains NamedPointer[] pointers") +
        variables.map { "${it.type.refineryType} ${it.name.refinerified}" }

  protected open val environmentSetup: String
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

  // Initial state

  protected open val initialStateDeclarations: List<String>
    get() = listOf("!exists(MemoryRegion::new).", "next_address($ENVIRONMENT): 1.")

  protected val initialState: String
    get() = initialStateDeclarations.joinToString("\n")

  // Transitions

  protected abstract val transitionDeclarations: List<String>

  protected val transitions: String
    get() = transitionDeclarations.joinToString("\n\n")

  // Error property

  protected abstract val errorProperty: String

  protected val errorDeclaration: String
    get() =
      """
      |@goal
      |pred error_property() <-> $errorProperty.
      """
        .trimMargin()

  // Top-level declarations

  protected val topLevelDeclaration: List<String>
    get() =
      listOf(
        "% --- METAMODEL ---",
        metamodel,
        regionExists,
        "% --- ENVIRONMENT SETUP ---",
        environmentSetup,
        invalidMemorySetup,
        "% --- INITIAL STATE ---",
        initialState,
        "% --- ERROR PROPERTY ---",
        errorDeclaration,
        "% --- TRANSITIONS ---",
        transitions,
      )

  protected val Type.refineryType: String
    get() =
      when (this) {
        is BoolType -> "boolean"
        is IntType -> "int"
        else -> error("Unsupported type in RefineryTransformationSystemBuilder: $this")
      }

  fun build(): String = topLevelDeclaration.joinToString("\n\n")
}
