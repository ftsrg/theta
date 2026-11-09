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
package hu.bme.mit.theta.xcfa.passes.concurrency

import hu.bme.mit.theta.core.decl.Decls.Var
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.Expr
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.passes.ProcedurePass
import hu.bme.mit.theta.xcfa.passes.changeVars
import hu.bme.mit.theta.xcfa.utils.collectVars
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Turns a thread-local global into a local of each procedure a thread runs, starting from the
 * variable's initial value. After inlining a thread's accesses are all in that procedure, and
 * [ReferenceElimination] gives an address-taken local a new object per execution, so threads get
 * distinct addresses too. A procedure still called here has no such single owner and is refused.
 */
class ThreadLocalVarPass(private val parseContext: ParseContext) : ProcedurePass {

  override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
    val threadLocals = builder.parent.getVars().filter { it.threadLocal }
    if (threadLocals.isEmpty()) return builder
    val used = builder.getEdges().flatMap { it.label.collectVars() }.toSet()
    val owned = threadLocals.filter { it.wrappedVar in used }
    if (owned.isEmpty()) return builder
    val called =
      builder.parent.getProcedures().any { proc ->
        proc.getEdges().any { edge ->
          edge.label.getFlatLabels().any { it is InvokeLabel && it.name == builder.name }
        }
      }
    if (called) {
      throw UnsupportedFrontendElementException(
        "Thread-local variable used in a procedure that could not be inlined: ${builder.name}"
      )
    }
    val locals =
      owned.associate { global ->
        val decl = global.wrappedVar
        val local = Var(decl.name, decl.type)
        builder.addVar(local)
        parseContext.metadata.create(
          local.ref,
          "cType",
          CComplexType.getType(decl.ref, parseContext),
        )
        Pair(decl as VarDecl<*>, local as VarDecl<*>)
      }
    val inits =
      owned.map { global ->
        val local = locals[global.wrappedVar]!! as VarDecl<Type>
        StmtLabel(AssignStmt.of(local, cast(global.initValue as Expr<*>, local.type)))
      }
    val edges = builder.getEdges().toList()
    edges.forEach { edge ->
      builder.removeEdge(edge)
      val label = edge.label.changeVars(locals)
      builder.addEdge(
        if (edge.source == builder.initLoc)
          edge.withLabel(SequenceLabel(inits + label, label.metadata))
        else edge.withLabel(label)
      )
    }
    return builder
  }
}
