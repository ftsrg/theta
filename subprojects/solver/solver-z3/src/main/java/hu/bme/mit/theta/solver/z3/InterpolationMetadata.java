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

import com.google.common.collect.Sets;
import com.microsoft.z3.*;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import java.util.Arrays;
import java.util.List;

record InterpolationMetadata(
        BoolExpr a,
        com.microsoft.z3.Expr<?>[] aSym,
        BoolExpr b,
        com.microsoft.z3.Expr<?>[] bSym,
        com.microsoft.z3.Expr<?>[] cSym) {
    InterpolationMetadata(Z3TransformationManager t, List<AndExpr> a, List<AndExpr> b) {
        this(
                (BoolExpr) t.toTerm(And(a)),
                ExprUtils.getConstants(a).stream()
                        .map(it -> t.toTerm(it.getRef()))
                        .toArray(com.microsoft.z3.Expr[]::new),
                (BoolExpr) t.toTerm(And(b)),
                ExprUtils.getConstants(b).stream()
                        .map(it -> t.toTerm(it.getRef()))
                        .toArray(com.microsoft.z3.Expr[]::new),
                Sets.intersection(ExprUtils.getConstants(a), ExprUtils.getConstants(b)).stream()
                        .map(it -> t.toTerm(it.getRef()))
                        .toArray(com.microsoft.z3.Expr[]::new));
    }

    BoolExpr interpolate(Context ctx) {
        Solver hornSolver = ctx.mkSolver("HORN");

        FuncDecl<BoolSort> A = ctx.mkFuncDecl("A", exprsToSorts(aSym), ctx.getBoolSort());
        FuncDecl<BoolSort> B = ctx.mkFuncDecl("B", exprsToSorts(bSym), ctx.getBoolSort());
        FuncDecl<BoolSort> itp = ctx.mkFuncDecl("itp", exprsToSorts(cSym), ctx.getBoolSort());

        // Rule 1: a => A(sA)
        BoolExpr rule1 = forallOrBody(ctx, aSym, ctx.mkImplies(a, A.apply(aSym)));
        hornSolver.add(rule1);

        // Rule 2: b => B(sB)
        BoolExpr rule2 = forallOrBody(ctx, bSym, ctx.mkImplies(b, B.apply(bSym)));
        hornSolver.add(rule2);

        // Rule 3: A(sA) => itp(sC)
        BoolExpr rule3 = forallOrBody(ctx, aSym, ctx.mkImplies(A.apply(aSym), itp.apply(cSym)));
        hornSolver.add(rule3);

        // Rule 4: itp(sC) ∧ B(sB) => false
        BoolExpr rule4 =
                forallOrBody(
                        ctx,
                        bSym,
                        ctx.mkImplies(ctx.mkAnd(itp.apply(cSym), B.apply(bSym)), ctx.mkFalse()));
        hornSolver.add(rule4);

        Status result = hornSolver.check();
        if (result != Status.SATISFIABLE) {
            return null;
        }
        final BoolExpr body = interpretation(ctx, hornSolver.getModel(), itp);
        // The interpretation speaks about itp's arguments as de Bruijn variables; cSym[i] is
        // argument i.
        return cSym.length == 0 ? body : (BoolExpr) body.substituteVars(cSym);
    }

    /**
     * The body of {@code itp}'s interpretation in {@code model}, over de Bruijn variables #0..#n-1
     * standing for its arguments.
     *
     * <p>A zero-arity declaration is a constant, and {@link Model#getFuncInterp} refuses those.
     * Otherwise the interpretation is an else branch plus point-wise entries, and every entry has
     * to be guarded by the arguments it applies to -- its value alone says nothing about the
     * function.
     */
    static BoolExpr interpretation(
            final Context ctx, final Model model, final FuncDecl<BoolSort> itp) {
        if (itp.getArity() == 0) {
            final com.microsoft.z3.Expr<?> constInterp = model.getConstInterp(itp);
            return constInterp == null ? ctx.mkFalse() : (BoolExpr) constInterp;
        }
        final FuncInterp<BoolSort> interp = model.getFuncInterp(itp);
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

    private static Sort[] exprsToSorts(Expr[] exprs) {
        return Arrays.stream(exprs).map(Expr::getSort).toArray(Sort[]::new);
    }

    /**
     * {@code ctx.mkForall} over zero bound variables throws ("number of bound variables is 0")
     * rather than treating it as the vacuous, semantically equivalent case: a universal quantifier
     * over no variables is just its body. Hit when {@code a} or {@code b} (the CEGAR path segment
     * being interpolated) has no free constants -- e.g. a closed/literal-only conjunct.
     */
    private static BoolExpr forallOrBody(
            Context ctx, com.microsoft.z3.Expr<?>[] vars, BoolExpr body) {
        return vars.length == 0 ? body : ctx.mkForall(vars, body, 1, null, null, null, null);
    }
}
