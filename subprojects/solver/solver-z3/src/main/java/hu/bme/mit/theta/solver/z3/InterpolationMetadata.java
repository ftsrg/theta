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
package hu.bme.mit.theta.solver.z3;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;

import com.google.common.collect.Sets;
import com.google.common.collect.Streams;
import com.microsoft.z3.*;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.utils.ExprUtils;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Stream;

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
        BoolExpr rule1 =
                ctx.mkForall(aSym, ctx.mkImplies(a, A.apply(aSym)), 1, null, null, null, null);
        hornSolver.add(rule1);

        // Rule 2: b => B(sB)
        BoolExpr rule2 =
                ctx.mkForall(bSym, ctx.mkImplies(b, B.apply(bSym)), 1, null, null, null, null);
        hornSolver.add(rule2);

        // Rule 3: A(sA) => itp(sC)
        BoolExpr rule3 =
                ctx.mkForall(
                        aSym,
                        ctx.mkImplies(A.apply(aSym), itp.apply(cSym)),
                        1,
                        null,
                        null,
                        null,
                        null);
        ;
        hornSolver.add(rule3);

        // Rule 4: itp(sC) ∧ B(sB) => false
        BoolExpr rule4 =
                ctx.mkForall(
                        bSym,
                        ctx.mkImplies(ctx.mkAnd(itp.apply(cSym), B.apply(bSym)), ctx.mkFalse()),
                        1,
                        null,
                        null,
                        null,
                        null);
        ;
        hornSolver.add(rule4);

        Status result = hornSolver.check();
        if (result == Status.SATISFIABLE) {
            final var interp = hornSolver.getModel().getFuncInterp(itp);
            final var values =
                    Streams.concat(
                            Arrays.stream(interp.getEntries()).map(FuncInterp.Entry::getValue),
                            Stream.of(interp.getElse()));
            BoolExpr answer = ctx.mkOr(values.toArray(BoolExpr[]::new));
            return (BoolExpr) answer.substituteVars(cSym);
        } else {
            return null;
        }
    }

    private static Sort[] exprsToSorts(Expr[] exprs) {
        return Arrays.stream(exprs).map(Expr::getSort).toArray(Sort[]::new);
    }
}
