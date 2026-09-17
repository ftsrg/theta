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
package hu.bme.mit.theta.solver.z3;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import com.microsoft.z3.*;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.solver.ItpMarkerTree;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * One Horn query for a whole interpolation pattern: a predicate per node of the marker tree, where
 * the children of a node imply that node and the root implies false. The solution of that query is
 * a tree interpolant by construction -- every node is entailed by its own subtree, contradicts the
 * rest of the pattern, and follows from its children. A sequence pattern is the chain case and a
 * binary pattern the two-node chain, so both come out of the same encoding.
 *
 * <p>Solving each cut on its own would leave consecutive interpolants unrelated, which does not
 * meet the {@link hu.bme.mit.theta.solver.ItpSolver} contract.
 */
final class InterpolationMetadata {

    /** A node of the pattern, in post-order: every child comes before its parent. */
    private record Node(
            Z3ItpMarker marker,
            BoolExpr term,
            com.microsoft.z3.Expr<?>[] own,
            com.microsoft.z3.Expr<?>[] shared,
            List<Integer> children) {}

    private final List<Node> nodes;

    InterpolationMetadata(final Z3TransformationManager t, final ItpMarkerTree<Z3ItpMarker> root) {
        final List<Z3ItpMarker> markers = new ArrayList<>();
        final List<hu.bme.mit.theta.core.type.Expr<BoolType>> exprs = new ArrayList<>();
        final List<List<Integer>> children = new ArrayList<>();
        final List<Set<ConstDecl<?>>> subtreeConsts = new ArrayList<>();
        flatten(root, markers, exprs, children, subtreeConsts);

        nodes = new ArrayList<>(markers.size());
        for (int i = 0; i < markers.size(); i++) {
            // Everything outside node i's subtree; what the subtree and that share is i's scope.
            final Set<ConstDecl<?>> outside = new LinkedHashSet<>();
            for (int j = 0; j < markers.size(); j++) {
                if (!isInSubtree(children, i, j)) {
                    outside.addAll(ExprUtils.getConstants(exprs.get(j)));
                }
            }
            nodes.add(
                    new Node(
                            markers.get(i),
                            (BoolExpr) t.toTerm(exprs.get(i)),
                            toTerms(t, ExprUtils.getConstants(exprs.get(i))),
                            toTerms(t, intersect(subtreeConsts.get(i), outside)),
                            children.get(i)));
        }
    }

    private static com.microsoft.z3.Expr<?>[] toTerms(
            final Z3TransformationManager t, final Set<ConstDecl<?>> consts) {
        return consts.stream()
                .map(it -> t.toTerm(it.getRef()))
                .toArray(com.microsoft.z3.Expr[]::new);
    }

    /** Post-order flattening of the marker tree; children land before their parent. */
    private static int flatten(
            final ItpMarkerTree<Z3ItpMarker> node,
            final List<Z3ItpMarker> markers,
            final List<hu.bme.mit.theta.core.type.Expr<BoolType>> exprs,
            final List<List<Integer>> children,
            final List<Set<ConstDecl<?>>> subtreeConsts) {
        final List<Integer> childIndices = new ArrayList<>();
        final Set<ConstDecl<?>> consts = new LinkedHashSet<>();
        for (final ItpMarkerTree<Z3ItpMarker> child : node.getChildren()) {
            final int childIndex = flatten(child, markers, exprs, children, subtreeConsts);
            childIndices.add(childIndex);
            consts.addAll(subtreeConsts.get(childIndex));
        }
        final hu.bme.mit.theta.core.type.Expr<BoolType> expr =
                And(node.getMarker().getTerms().stream().toList());
        consts.addAll(ExprUtils.getConstants(expr));

        markers.add(node.getMarker());
        exprs.add(expr);
        children.add(childIndices);
        subtreeConsts.add(consts);
        return markers.size() - 1;
    }

    private static boolean isInSubtree(
            final List<List<Integer>> children, final int root, final int node) {
        if (root == node) {
            return true;
        }
        for (final int child : children.get(root)) {
            if (isInSubtree(children, child, node)) {
                return true;
            }
        }
        return false;
    }

    private static Set<ConstDecl<?>> intersect(
            final Set<ConstDecl<?>> a, final Set<ConstDecl<?>> b) {
        final Set<ConstDecl<?>> result = new LinkedHashSet<>(a);
        result.retainAll(b);
        return result;
    }

    /**
     * The interpolant of every marker, or null when the Horn solver cannot answer. The root always
     * maps to false.
     */
    Map<Z3ItpMarker, BoolExpr> interpolate(final Context ctx) {
        final Solver hornSolver = ctx.mkSolver("HORN");
        final int rootIndex = nodes.size() - 1;

        final List<FuncDecl<BoolSort>> preds = new ArrayList<>();
        for (int i = 0; i < nodes.size(); i++) {
            preds.add(
                    ctx.mkFuncDecl(
                            "itp!" + i, exprsToSorts(nodes.get(i).shared()), ctx.getBoolSort()));
        }

        for (int i = 0; i < nodes.size(); i++) {
            final Node node = nodes.get(i);
            final List<BoolExpr> body = new ArrayList<>();
            final Set<com.microsoft.z3.Expr<?>> bound = new LinkedHashSet<>();
            for (final int child : node.children()) {
                body.add((BoolExpr) preds.get(child).apply(nodes.get(child).shared()));
                bound.addAll(Arrays.asList(nodes.get(child).shared()));
            }
            body.add(node.term());
            bound.addAll(Arrays.asList(node.own()));
            bound.addAll(Arrays.asList(node.shared()));

            final BoolExpr head =
                    i == rootIndex ? ctx.mkFalse() : (BoolExpr) preds.get(i).apply(node.shared());
            hornSolver.add(
                    forallOrBody(
                            ctx,
                            bound.toArray(com.microsoft.z3.Expr[]::new),
                            ctx.mkImplies(ctx.mkAnd(body.toArray(BoolExpr[]::new)), head)));
        }

        if (hornSolver.check() != Status.SATISFIABLE) {
            return null;
        }
        final Model model = hornSolver.getModel();
        final Map<Z3ItpMarker, BoolExpr> result = new LinkedHashMap<>();
        for (int i = 0; i < nodes.size(); i++) {
            final Node node = nodes.get(i);
            if (i == rootIndex) {
                result.put(node.marker(), ctx.mkFalse());
            } else {
                final BoolExpr body = interpretation(ctx, model, preds.get(i));
                // The interpretation speaks about the predicate's arguments as de Bruijn
                // variables; shared[i] is argument i.
                result.put(
                        node.marker(),
                        node.shared().length == 0
                                ? body
                                : (BoolExpr) body.substituteVars(node.shared()));
            }
        }
        return result;
    }

    /**
     * The body of {@code pred}'s interpretation in {@code model}, over de Bruijn variables #0..#n-1
     * standing for its arguments.
     *
     * <p>A zero-arity declaration is a constant, and {@link Model#getFuncInterp} refuses those.
     * Otherwise the interpretation is an else branch plus point-wise entries, and every entry has
     * to be guarded by the arguments it applies to -- its value alone says nothing about the
     * function.
     */
    static BoolExpr interpretation(
            final Context ctx, final Model model, final FuncDecl<BoolSort> pred) {
        if (pred.getArity() == 0) {
            final com.microsoft.z3.Expr<?> constInterp = model.getConstInterp(pred);
            return constInterp == null ? ctx.mkFalse() : (BoolExpr) constInterp;
        }
        final FuncInterp<BoolSort> interp = model.getFuncInterp(pred);
        if (interp == null) {
            return ctx.mkFalse();
        }
        BoolExpr body = interp.getElse() == null ? ctx.mkFalse() : (BoolExpr) interp.getElse();
        for (final FuncInterp.Entry<BoolSort> entry : interp.getEntries()) {
            final com.microsoft.z3.Expr<?>[] args = entry.getArgs();
            final BoolExpr[] match = new BoolExpr[args.length];
            for (int i = 0; i < args.length; i++) {
                match[i] = ctx.mkEq(ctx.mkBound(i, args[i].getSort()), args[i]);
            }
            body = (BoolExpr) ctx.mkITE(ctx.mkAnd(match), entry.getValue(), body);
        }
        return body;
    }

    private static Sort[] exprsToSorts(final com.microsoft.z3.Expr<?>[] exprs) {
        return Arrays.stream(exprs).map(com.microsoft.z3.Expr::getSort).toArray(Sort[]::new);
    }

    /**
     * {@code ctx.mkForall} over zero bound variables throws ("number of bound variables is 0")
     * rather than treating it as the vacuous, semantically equivalent case: a universal quantifier
     * over no variables is just its body. Hit when a marker has no free constants -- e.g. a
     * closed/literal-only conjunct.
     */
    private static BoolExpr forallOrBody(
            final Context ctx, final com.microsoft.z3.Expr<?>[] vars, final BoolExpr body) {
        return vars.length == 0 ? body : ctx.mkForall(vars, body, 1, null, null, null, null);
    }
}
