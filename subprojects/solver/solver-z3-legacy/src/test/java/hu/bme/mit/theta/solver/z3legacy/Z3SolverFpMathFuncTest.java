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
package hu.bme.mit.theta.solver.z3legacy;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpAssign;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.FpType;
import static hu.bme.mit.theta.core.type.fptype.FpExprs.MathFunc;
import static org.junit.jupiter.api.Assertions.assertEquals;

import com.microsoft.z3legacy.Context;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.fptype.FpMathFuncExpr.Function;
import hu.bme.mit.theta.core.type.fptype.FpType;
import hu.bme.mit.theta.core.utils.FpUtils;
import hu.bme.mit.theta.solver.Solver;
import hu.bme.mit.theta.solver.SolverStatus;
import org.junit.jupiter.api.Test;

public class Z3SolverFpMathFuncTest {

    private static final FpType FLOAT = FpType(8, 24);

    private static SolverStatus check(final Expr<hu.bme.mit.theta.core.type.booltype.BoolType> e) {
        try (Solver solver = Z3LegacySolverFactory.getInstance().createSolver()) {
            solver.add(e);
            return solver.check();
        } catch (Exception ex) {
            throw new RuntimeException(ex);
        }
    }

    @Test
    public void equalArgumentsGiveEqualResults() {
        final ConstDecl<FpType> x = Const("x", FLOAT);
        final ConstDecl<FpType> y = Const("y", FLOAT);
        final var differ =
                Not(
                        FpAssign(
                                MathFunc(Function.EXP, x.getRef()),
                                MathFunc(Function.EXP, y.getRef())));
        assertEquals(SolverStatus.UNSAT, check(And(FpAssign(x.getRef(), y.getRef()), differ)));
    }

    @Test
    public void resultIsUninterpreted() {
        final var one = FpUtils.fromString("1.0", FLOAT);
        final var hundred = FpUtils.fromString("100.0", FLOAT);
        assertEquals(SolverStatus.SAT, check(FpAssign(MathFunc(Function.EXP, one), hundred)));
    }

    @Test
    public void functionsAndSortsAreDistinct() {
        final ConstDecl<FpType> x = Const("x", FLOAT);
        final var sinEqCos =
                FpAssign(
                        MathFunc(Function.SIN, x.getRef()),
                        MathFunc(Function.COS, x.getRef()));
        assertEquals(SolverStatus.SAT, check(Not(sinEqCos)));
    }

    @Test
    public void termRoundTrip() {
        final ConstDecl<FpType> x = Const("x", FLOAT);
        final Context context = new Context();
        final Z3SymbolTable symbolTable = new Z3SymbolTable();
        final Z3TypeSymbolTable typeSymbolTable = new Z3TypeSymbolTable();
        final var manager = new Z3TransformationManager(symbolTable, typeSymbolTable, context);
        final var termTransformer = new Z3TermTransformer(symbolTable, typeSymbolTable);
        for (final Function f : Function.values()) {
            final var expr = MathFunc(f, x.getRef());
            assertEquals(expr, termTransformer.toExpr(manager.toTerm(expr)));
        }
        context.close();
    }
}
