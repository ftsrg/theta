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
import java.util.IdentityHashMap;
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

    /** A node of the pattern, together with the children whose interpolants imply it. */
    private record Node(
            Z3ItpMarker marker,
            BoolExpr term,
            com.microsoft.z3.Expr<?>[] own,
            com.microsoft.z3.Expr<?>[] shared,
            List<Node> children) {}

    /** Every node of the pattern, children before their parent, so the root comes last. */
    private final List<Node> nodes;

    InterpolationMetadata(final Z3TransformationManager t, final ItpMarkerTree<Z3ItpMarker> root) {
        final Map<ItpMarkerTree<Z3ItpMarker>, Set<ConstDecl<?>>> subtreeConsts =
                new IdentityHashMap<>();
        collectConsts(root, subtreeConsts);
        nodes = new ArrayList<>();
        build(t, root, Set.of(), subtreeConsts, nodes);
    }

    /** The constants of a whole subtree, for that subtree and every subtree below it. */
    private static Set<ConstDecl<?>> collectConsts(
            final ItpMarkerTree<Z3ItpMarker> tree,
            final Map<ItpMarkerTree<Z3ItpMarker>, Set<ConstDecl<?>>> subtreeConsts) {
        final Set<ConstDecl<?>> consts = new LinkedHashSet<>(ExprUtils.getConstants(exprOf(tree)));
        for (final ItpMarkerTree<Z3ItpMarker> child : tree.getChildren()) {
            consts.addAll(collectConsts(child, subtreeConsts));
        }
        subtreeConsts.put(tree, consts);
        return consts;
    }

    /**
     * Builds {@code tree} and everything below it into {@code nodes}, children first. {@code
     * outside} holds the constants of every node outside this subtree; what the subtree shares with
     * them is this node's scope.
     */
    private static Node build(
            final Z3TransformationManager t,
            final ItpMarkerTree<Z3ItpMarker> tree,
            final Set<ConstDecl<?>> outside,
            final Map<ItpMarkerTree<Z3ItpMarker>, Set<ConstDecl<?>>> subtreeConsts,
            final List<Node> nodes) {
        final hu.bme.mit.theta.core.type.Expr<BoolType> expr = exprOf(tree);
        final Set<ConstDecl<?>> own = ExprUtils.getConstants(expr);

        final List<Node> children = new ArrayList<>(tree.getChildrenNumber());
        for (final ItpMarkerTree<Z3ItpMarker> child : tree.getChildren()) {
            // Outside a child's subtree: whatever is outside this one, this node's own assertions
            // and the sibling subtrees.
            final Set<ConstDecl<?>> childOutside = new LinkedHashSet<>(outside);
            childOutside.addAll(own);
            for (final ItpMarkerTree<Z3ItpMarker> sibling : tree.getChildren()) {
                if (sibling != child) {
                    childOutside.addAll(subtreeConsts.get(sibling));
                }
            }
            children.add(build(t, child, childOutside, subtreeConsts, nodes));
        }

        final Set<ConstDecl<?>> shared = new LinkedHashSet<>(subtreeConsts.get(tree));
        shared.retainAll(outside);

        final Node node =
                new Node(
                        tree.getMarker(),
                        (BoolExpr) t.toTerm(expr),
                        toTerms(t, own),
                        toTerms(t, shared),
                        children);
        nodes.add(node);
        return node;
    }

    private static hu.bme.mit.theta.core.type.Expr<BoolType> exprOf(
            final ItpMarkerTree<Z3ItpMarker> tree) {
        return And(tree.getMarker().getTerms().stream().toList());
    }

    private static com.microsoft.z3.Expr<?>[] toTerms(
            final Z3TransformationManager t, final Set<ConstDecl<?>> consts) {
        return consts.stream()
                .map(it -> t.toTerm(it.getRef()))
                .toArray(com.microsoft.z3.Expr[]::new);
    }

    /**
     * The interpolant of every marker, or null when the Horn solver cannot answer. The root always
     * maps to false.
     */
    Map<Z3ItpMarker, BoolExpr> interpolate(final Context ctx) {
        final Solver hornSolver = ctx.mkSolver("HORN");
        final Node root = nodes.get(nodes.size() - 1);

        final Map<Node, FuncDecl<BoolSort>> preds = new IdentityHashMap<>();
        for (int i = 0; i < nodes.size(); i++) {
            final Node node = nodes.get(i);
            preds.put(
                    node,
                    ctx.mkFuncDecl("itp!" + i, exprsToSorts(node.shared()), ctx.getBoolSort()));
        }

        for (final Node node : nodes) {
            final List<BoolExpr> body = new ArrayList<>();
            final Set<com.microsoft.z3.Expr<?>> bound = new LinkedHashSet<>();
            for (final Node child : node.children()) {
                body.add((BoolExpr) preds.get(child).apply(child.shared()));
                bound.addAll(Arrays.asList(child.shared()));
            }
            body.add(node.term());
            bound.addAll(Arrays.asList(node.own()));
            bound.addAll(Arrays.asList(node.shared()));

            final BoolExpr head =
                    node == root ? ctx.mkFalse() : (BoolExpr) preds.get(node).apply(node.shared());
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
        for (final Node node : nodes) {
            if (node == root) {
                result.put(node.marker(), ctx.mkFalse());
            } else {
                final BoolExpr body = interpretation(ctx, model, preds.get(node));
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
