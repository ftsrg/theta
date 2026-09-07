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
package hu.bme.mit.theta.xcfa.utils

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.Stmts.Assign
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.frontend.transformation.model.types.complex.compound.CPointer
import hu.bme.mit.theta.xcfa.model.InvokeLabel
import hu.bme.mit.theta.xcfa.model.SequenceLabel
import hu.bme.mit.theta.xcfa.model.StmtLabel
import hu.bme.mit.theta.xcfa.model.XcfaBuilder
import hu.bme.mit.theta.xcfa.model.XcfaGlobalVar
import hu.bme.mit.theta.xcfa.model.XcfaLabel
import hu.bme.mit.theta.xcfa.model.XcfaProcedureBuilder

/**
 * The number of pointer-base residue classes: every memory object has a base id, and the id modulo
 * this says what kind of object it is.
 *
 * | residue | kind                         | minted by                                       |
 * |---------|------------------------------|-------------------------------------------------|
 * | `3k+0`  | heap (`malloc`, `calloc`)    | `MallocFunctionPass`, from [mallocVar]          |
 * | `3k+1`  | static objects, and `alloca` | the frontend builder, then `AllocaFunctionPass` |
 * | `3k+2`  | address-taken locals         | `ReferenceElimination`                          |
 *
 * The classes never overlap. Both runtime kinds take their ids from the single [mallocVar] counter,
 * which advances by 3 per allocation so each allocation consumes its own `k`, and
 * `ReferenceElimination` has a compile-time counter of its own in a class no runtime allocation
 * uses. The one class with two producers is `3k+1`, where the counter is seeded past the frontend's
 * last compile-time base (see [ALLOCATION_STATIC_BASE_LIMIT]).
 *
 * The distinction matters to memsafety: `MemsafetyPass` accepts a `free` only of `3k+0` and its
 * memcleanup scan enumerates only `3k+0`, so a block the program is not responsible for freeing --
 * an `alloca`, a local's address -- must not be in that class.
 */
const val POINTER_BASE_CLASSES = 3

/**
 * [XcfaBuilder.metaData] key under which the frontend publishes the first compile-time base id it
 * did *not* hand out to a static object. Absent means no compile-time bases were minted.
 */
const val ALLOCATION_STATIC_BASE_LIMIT = "staticBaseLimit"

private val mallocVars: MutableMap<XcfaBuilder, VarDecl<*>> = mutableMapOf()

/**
 * The shared allocation counter. `malloc` and `alloca` hand out addresses from the same one, so
 * that a heap block and a stack block can never be given the same base.
 */
fun XcfaBuilder.mallocVar(parseContext: ParseContext): VarDecl<*> =
  mallocVars.getOrPut(this) { Var("__malloc", CPointer(null, null, parseContext).smtType) }

/**
 * Where the allocation counter starts: the smallest multiple of three at or above the compile-time
 * high-water mark, so that a runtime block can never be given the address of a static object.
 */
private fun XcfaBuilder.allocationSeed(): Int {
  val limit = (metaData[ALLOCATION_STATIC_BASE_LIMIT] as? Int) ?: 0
  return ((limit + POINTER_BASE_CLASSES - 1) / POINTER_BASE_CLASSES) * POINTER_BASE_CLASSES
}

/**
 * Creates the shared allocation counter and seeds it in the init procedure, once per XCFA. Does
 * nothing if the counter already exists.
 *
 * Must be called *before* a pass starts iterating a snapshot of its own edges: seeding replaces
 * every outgoing edge of the init procedure's `initLoc`, so an edge captured beforehand is stale
 * and removing it later fails.
 */
fun XcfaBuilder.ensureMallocVar(parseContext: ParseContext, retType: CComplexType) {
  val mallocVar = mallocVar(parseContext)
  if (getVars().any { it.wrappedVar == mallocVar }) return
  val seed = retType.getValue(allocationSeed().toString())
  addVar(XcfaGlobalVar(mallocVar, seed))
  val initProc = getInitProcedures().map { it.first }
  check(initProc.size == 1) { "Multiple start procedure are not handled well" }
  initProc.forEach { proc ->
    val initAssign = StmtLabel(Assign(cast(mallocVar, mallocVar.type), cast(seed, mallocVar.type)))
    val oldEdges = proc.initLoc.outgoingEdges.toList()
    val newEdges =
      oldEdges.map {
        it.withLabel(
          SequenceLabel(listOf(initAssign) + it.label.getFlatLabels(), it.label.metadata)
        )
      }
    oldEdges.forEach(proc::removeEdge)
    newEdges.forEach(proc::addEdge)
  }
}

/**
 * The C type the first allocation call matching [predicate] writes its base into, or null when this
 * procedure performs no such allocation. Lets the counter be seeded before the rewrite loop,
 * without needing an allocation site in hand.
 */
fun XcfaProcedureBuilder.firstAllocationRetType(
  parseContext: ParseContext,
  predicate: (XcfaLabel) -> Boolean,
): CComplexType? =
  getEdges()
    .asSequence()
    .flatMap { it.getFlatLabels().asSequence() }
    .filter(predicate)
    .map { CComplexType.getType((it as InvokeLabel).params[0], parseContext) }
    .firstOrNull()
