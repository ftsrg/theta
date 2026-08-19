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
package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.Decls
import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.stmt.AssignStmt
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.core.utils.TypeUtils.cast
import hu.bme.mit.theta.frontend.ParseContext
import hu.bme.mit.theta.frontend.UnsupportedFrontendElementException
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType
import hu.bme.mit.theta.xcfa.model.*
import hu.bme.mit.theta.xcfa.utils.defaultValue
import hu.bme.mit.theta.xcfa.utils.getFlatLabels

/**
 * Splicing a called procedure's body into its caller, shared by the two places that need it:
 * [InlineProceduresPass], which inlines a whole program up front, and [LoopUnrollPass], which
 * expands recursive calls to a bound and can therefore be re-run at a larger bound.
 */

/** A fresh copy of this location for a spliced-in body; never initial, final or error. */
internal fun XcfaLocation.inlinedCopy(): XcfaLocation =
  copy(name = name + XcfaLocation.uniqueCounter(), initial = false, final = false, error = false)

/** True when [label] calls a procedure this builder's program actually defines. */
internal fun XcfaProcedureBuilder.callsKnownProcedure(label: XcfaLabel): Boolean =
  label is InvokeLabel && parent.getProcedures().any { p -> p.name == label.name }

/** The procedure [label] calls, or null when the program does not define it. */
internal fun XcfaProcedureBuilder.calleeOf(label: InvokeLabel): XcfaProcedureBuilder? =
  parent.getProcedures().find { p -> p.name == label.name }

/**
 * The names of the procedures that can reach themselves through calls, direct or mutual.
 *
 * Computed from the bodies as they currently stand rather than through
 * [XcfaProcedureBuilder.canInline]: that helper caches its answer in `metaData` and folds together
 * "is recursive" with "reaches something recursive", both of which make it unreliable for a caller
 * that expands recursion incrementally and re-runs at a larger bound.
 */
internal fun recursiveProcedureNames(parent: XcfaBuilder): Set<String> {
  val callees =
    parent.getProcedures().associate { p ->
      p.name to
        p.getEdges()
          .flatMap { it.getFlatLabels() }
          .filterIsInstance<InvokeLabel>()
          .mapTo(mutableSetOf()) { it.name }
    }
  return callees.keys.filterTo(mutableSetOf()) { start ->
    val seen = mutableSetOf<String>()
    val stack = ArrayDeque(callees[start] ?: emptySet())
    var reachesItself = false
    while (stack.isNotEmpty()) {
      val next = stack.removeFirst()
      if (next == start) {
        reachesItself = true
        break
      }
      if (seen.add(next)) callees[next]?.let { stack.addAll(it) }
    }
    reachesItself
  }
}

/**
 * A procedure's body captured at a point in time: locations, edges, variables and parameters.
 *
 * Splicing has to work from a copy, not from the live builder. Expanding a *self*-recursive call
 * makes the callee and the caller the same object, so reading the live collections while adding to
 * them would either fail outright or -- worse -- silently splice a body from which the recursive
 * call had just been removed, truncating the recursion to a single level with nothing to show that
 * it happened.
 */
internal class ProcedureBody(
  val locs: List<XcfaLocation>,
  val edges: List<XcfaEdge>,
  val vars: List<VarDecl<*>>,
  val params: List<Pair<VarDecl<*>, ParamDirection>>,
  val initLoc: XcfaLocation,
  val finalLoc: java.util.Optional<XcfaLocation>,
  val errorLoc: java.util.Optional<XcfaLocation>,
)

/** Captures this procedure's body as it stands right now; see [ProcedureBody]. */
internal fun XcfaProcedureBuilder.snapshotBody(): ProcedureBody =
  ProcedureBody(
    locs = ArrayList(getLocs()),
    edges = ArrayList(getEdges()),
    vars = ArrayList(getVars()),
    params = ArrayList(getParams()),
    initLoc = initLoc,
    finalLoc = finalLoc,
    errorLoc = errorLoc,
  )

/**
 * Splices [callee]'s body into [builder] in place of a call, so that control flows
 * `source -> (copy of callee) -> target`.
 *
 * The caller is responsible for having removed the edge that carried [invokeLabel] and for bringing
 * [callee] to whatever optimization phase it needs: this only performs the splice, so that a caller
 * expanding recursion to a bound can splice a body repeatedly without driving the pass pipeline.
 */
internal fun inlineCallSite(
  builder: XcfaProcedureBuilder,
  source: XcfaLocation,
  target: XcfaLocation,
  invokeLabel: InvokeLabel,
  callee: ProcedureBody,
  parseContext: ParseContext,
  metadata: MetaData,
  freshFrame: Boolean = false,
) {
  val calleeLocs = callee.locs
  val calleeEdges = callee.edges

  // With [freshFrame], the spliced copy gets its own locals and parameters. Sharing them is
  // harmless when a procedure is inlined once per path, but recursive frames *nest*: without this
  // the inner `sum(n-1)` writes the very `n` its caller is still using, so the guards of the outer
  // frames read the innermost value. That corrupts the program rather than bounding it, and shows
  // up as verdicts that are wrong in both directions.
  val frame: Map<VarDecl<*>, VarDecl<*>> =
    if (!freshFrame) emptyMap()
    else
      (callee.vars + callee.params.map { it.first }).distinct().associateWith { v ->
        Decls.Var("${v.name}_inl${XcfaLocation.uniqueCounter()}", v.type)
      }
  val calleeVars = callee.vars.map { frame[it] ?: it }
  val calleeParams = callee.params.map { (v, dir) -> (frame[v] ?: v) to dir }

  val newLocs: MutableMap<XcfaLocation, XcfaLocation> = LinkedHashMap()
  calleeLocs.forEach { newLocs[it] = it.inlinedCopy() }
  calleeVars.forEach { builder.addVar(it) }
  calleeParams.forEach { builder.addVar(it.first) }
  calleeEdges.forEach {
    val relabeled = if (frame.isEmpty()) it.label else it.label.changeVars(frame)
    builder.addEdge(
      it
        .withLabel(relabeled)
        .withSource(checkNotNull(newLocs[it.source]))
        .withTarget(checkNotNull(newLocs[it.target]))
    )
  }

  val inStmts: MutableList<XcfaLabel> = ArrayList()
  val outStmts: MutableList<XcfaLabel> = ArrayList()

  // Give every variable this splice invents a definite starting value. The IN parameters are
  // assigned from the call arguments just below, but the locals and the OUT parameters are not, and
  // a callee that never writes one -- a void function never writes the `_ret` variable the frontend
  // invents for it -- leaves the caller's write-back reading a variable that was never assigned.
  // The OC checker refuses such a task outright ("variable ... is not initialized"); other backends
  // quietly explore a havoc'd value, which is worse. Only the freshly framed copies need this:
  // without renaming these are the callee's own declarations, which the program initialises itself.
  val assignedFromArgs =
    calleeParams.filter { it.second != ParamDirection.OUT }.mapTo(mutableSetOf()) { it.first }
  if (frame.isNotEmpty()) {
    (calleeVars + calleeParams.map { it.first })
      .distinct()
      .filter { it !in assignedFromArgs }
      .forEach { v ->
        inStmts.add(
          StmtLabel(
            AssignStmt.of(cast(v, v.type), cast(v.type.defaultValue, v.type)),
            metadata = EmptyMetaData,
          )
        )
      }
  }

  // The call site and the callee must agree on arity, and when they do not, indexing
  // `invokeLabel.params` by the callee's parameter position walks off the end: the whole file died
  // with a bare `IndexOutOfBoundsException` naming neither the procedure nor the counts
  // (`ddv-machzwd/ddv_machzwd_*`, uncovered once the dimensionless-array fix let them get this
  // far).
  //
  // ⚠️ The mismatch seen there is *internal*, not a defect in the C: `void outb(unsigned char,
  // unsigned int)` is declared with two parameters and every call passes two, yet the callee
  // arrives with three -- an only-declared `void` function gets a synthetic return slot its call
  // sites do not supply. So this refusal deliberately does NOT blame the source; it reports the
  // disagreement and stops. An honest refusal and an unexplained crash both score 0, but only one
  // of them can be acted on.
  //
  // ⚠️ Only a callee with MORE parameters than the call site supplies is a problem. The loop below
  // walks `calleeParams` and indexes `invokeLabel.params[i]`, so that is the direction that runs off
  // the end. A call site supplying *extra* arguments -- which is every variadic call, `printk(fmt,
  // ...)` and friends -- indexes safely and simply ignores the surplus, exactly as it did before
  // this guard existed. Refusing those too cost 713 LDV driver runs that used to build (`printk`
  // 476, `dev_err` 158, `__dynamic_dev_dbg` 79), the bulk of the run-91 parse regression.
  // A `void` procedure carries a SYNTHETIC return slot -- FrontendXcfaBuilder mints
  // `<name>_ret` for every procedure, void included, because the rest of the pipeline assumes a
  // return variable exists. A call site that discards the (nonexistent) result does not pass one,
  // so the callee has exactly one parameter more than the call supplies and the two disagree by
  // that slot alone. `void outb(unsigned char, unsigned int)` is declared with two parameters and
  // every call passes two, yet the callee arrives with three:
  //   call   [(Bv 1), (Bv 32)]
  //   callee [(outb_ret, OUT), (outb::byte, IN), (outb::port, IN)]
  // Refusing that is refusing our own bookkeeping. Bind the callee's real parameters to the
  // arguments and drop the return slot: a void function has no result for anyone to read, so
  // nothing is lost. Anything OTHER than this exact shape is still refused.
  val voidReturnSlotUnpassed =
    calleeParams.size == invokeLabel.params.size + 1 &&
      calleeParams.isNotEmpty() &&
      calleeParams[0].second == ParamDirection.OUT &&
      calleeParams[0].first.name == "${invokeLabel.name}_ret"
  @Suppress("NAME_SHADOWING")
  val effectiveParams = if (voidReturnSlotUnpassed) calleeParams.drop(1) else calleeParams

  if (effectiveParams.size > invokeLabel.params.size) {
    throw UnsupportedFrontendElementException(
      "Inlining '${invokeLabel.name}': the call site supplies ${invokeLabel.params.size}" +
        " argument(s) ${invokeLabel.params.map { it.type }} but the procedure has" +
        " ${effectiveParams.size} parameter(s) ${effectiveParams.map { it.first.name to it.second }}." +
        " This is an internal disagreement, not necessarily a fault in the input."
    )
  }

  for ((i, param) in effectiveParams.withIndex()) {
    if (param.second != ParamDirection.OUT) {
      val stmt =
        AssignStmt.of(
          cast(param.first, param.first.type),
          cast(
            CComplexType.getType(param.first.ref, parseContext).castTo(invokeLabel.params[i]),
            param.first.type,
          ),
        )
      inStmts.add(StmtLabel(stmt, metadata = EmptyMetaData))
    }

    if (param.second != ParamDirection.IN) {
      val varDecl = (invokeLabel.params[i] as RefExpr<*>).decl as VarDecl<*>
      // This writes the callee's result into the *caller's* variable, so it is the caller's type
      // that the assignment has to be built at -- and the right-hand side already converts to it.
      // Naming the callee's type here instead is indistinguishable whenever the two agree, and they
      // nearly always do; but a call through a function pointer has no signature to go by, so the
      // frontend types its result an `int` while the function it dispatches to may return anything
      // -- `void`, say, whereupon this asked to cast a 32-bit variable to a 1-bit one and threw.
      val stmt =
        AssignStmt.of(
          cast(varDecl, varDecl.type),
          cast(CComplexType.getType(varDecl.ref, parseContext).castTo(param.first.ref), varDecl.type),
        )
      outStmts.add(StmtLabel(stmt, metadata = EmptyMetaData))
    }
  }

  val initLoc = callee.initLoc
  val finalLoc = callee.finalLoc
  val errorLoc = callee.errorLoc

  builder.addEdge(
    XcfaEdge(source, checkNotNull(newLocs[initLoc]), SequenceLabel(inStmts), metadata)
  )
  if (finalLoc.isPresent)
    builder.addEdge(
      XcfaEdge(
        checkNotNull(newLocs[finalLoc.get()]),
        target,
        SequenceLabel(outStmts),
        EmptyMetaData,
      )
    )
  if (errorLoc.isPresent) {
    if (builder.errorLoc.isEmpty) builder.createErrorLoc()
    builder.addEdge(
      XcfaEdge(
        checkNotNull(newLocs[errorLoc.get()]),
        builder.errorLoc.get(),
        SequenceLabel(listOf(NopLabel)),
        EmptyMetaData,
      )
    )
  }
}
