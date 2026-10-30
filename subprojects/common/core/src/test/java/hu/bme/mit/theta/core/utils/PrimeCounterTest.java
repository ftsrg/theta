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
package hu.bme.mit.theta.core.utils;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.anytype.Exprs.Prime;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Iff;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static java.util.Arrays.asList;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.dsl.CoreDslManager;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.PrimeExpr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.indexings.BasicVarIndexing.BasicVarIndexingBuilder;
import hu.bme.mit.theta.core.utils.indexings.VarIndexing;
import hu.bme.mit.theta.core.utils.indexings.VarIndexingFactory;
import java.time.Duration;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Random;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;

public final class PrimeCounterTest {
    public String exprString;
    public int nPrimesOnX;
    public int nPrimesOnY;

    public static Collection<Object[]> data() {
        return asList(
                new Object[][] {
                    {"true", 0, 0},
                    {"(true)'", 0, 0},
                    {"x", 0, 0},
                    {"not x'", 1, 0},
                    {"x''", 2, 0},
                    {"x' and y", 1, 0},
                    {"(x imply y)'", 1, 1},
                    {"(x' iff y)'", 2, 1},
                    {"a", 0, 0},
                    {"a'", 0, 0},
                    {"x' and a", 1, 0},
                    {"(x' or a)'", 2, 0}
                });
    }

    @MethodSource("data")
    @ParameterizedTest
    public void test(String exprString, int nPrimesOnX, int nPrimesOnY) {
        initPrimeCounterTest(exprString, nPrimesOnX, nPrimesOnY);
        // Arrange
        final ConstDecl<BoolType> a = Const("a", Bool());
        final VarDecl<BoolType> x = Var("x", Bool());
        final VarDecl<BoolType> y = Var("y", Bool());

        final CoreDslManager manager = new CoreDslManager();
        manager.declare(a);
        manager.declare(x);
        manager.declare(y);

        final Expr<?> expr = manager.parseExpr(exprString);

        // Act
        final VarIndexing indexing = PathUtils.countPrimes(expr);

        // Assert
        assertEquals(nPrimesOnX, indexing.get(x));
        assertEquals(nPrimesOnY, indexing.get(y));
    }

    public void initPrimeCounterTest(String exprString, int nPrimesOnX, int nPrimesOnY) {
        this.exprString = exprString;
        this.nPrimesOnX = nPrimesOnX;
        this.nPrimesOnY = nPrimesOnY;
    }

    @Test
    public void testSameAsJoinOfOperands() {
        final List<VarDecl<BoolType>> vars = new ArrayList<>();
        for (int i = 0; i < 20; i++) {
            vars.add(Var("v" + i, Bool()));
        }
        final ConstDecl<BoolType> c = Const("c", Bool());

        for (int seed = 0; seed < 50; seed++) {
            final Expr<BoolType> expr = randomExpr(new Random(seed), vars, c, 8);

            final VarIndexing expected = joinOfOperands(expr, 0).build();
            final VarIndexing actual = PrimeCounter.countPrimes(expr);

            assertEquals(expected.toString(), actual.toString());
            for (final VarDecl<BoolType> v : vars) {
                assertEquals(expected.get(v), actual.get(v));
            }
        }
    }

    @Test
    public void testLargeFlatConjunction() {
        // Shaped like an AIGER-derived transition relation: a definition and its primed copy
        // per gate in one flat conjunction, so almost every variable ends up primed.
        final int n = 50_000;
        final List<VarDecl<BoolType>> vars = new ArrayList<>(n);
        for (int i = 0; i < n; i++) {
            vars.add(Var("v" + i, Bool()));
        }
        final List<Expr<BoolType>> conjuncts = new ArrayList<>(2 * n);
        final int[] expected = new int[n];
        for (int i = 1; i < n; i++) {
            final int j = i / 2;
            final Expr<BoolType> def =
                    Iff(vars.get(i).getRef(), And(vars.get(i - 1).getRef(), vars.get(j).getRef()));
            final int primes = i % 3 == 0 ? 2 : 1;
            conjuncts.add(def);
            conjuncts.add(primes == 2 ? Prime(Prime(def)) : Prime(def));
            for (final int k : new int[] {i, i - 1, j}) {
                expected[k] = Math.max(expected[k], primes);
            }
        }
        final Expr<BoolType> expr = And(conjuncts);

        final VarIndexing indexing =
                assertTimeoutPreemptively(
                        Duration.ofSeconds(2), () -> PrimeCounter.countPrimes(expr));

        for (int i = 0; i < n; i++) {
            assertEquals(expected[i], indexing.get(vars.get(i)));
        }
    }

    private static Expr<BoolType> randomExpr(
            final Random random,
            final List<VarDecl<BoolType>> vars,
            final ConstDecl<BoolType> c,
            final int depth) {
        final int choice = depth == 0 ? random.nextInt(2) : random.nextInt(10);
        switch (choice) {
            case 0:
                return vars.get(random.nextInt(vars.size())).getRef();
            case 1:
                return c.getRef();
            case 2:
            case 3:
                return Prime(randomExpr(random, vars, c, depth - 1));
            case 4:
                return Not(randomExpr(random, vars, c, depth - 1));
            case 5:
                return Iff(
                        randomExpr(random, vars, c, depth - 1),
                        randomExpr(random, vars, c, depth - 1));
            default:
                final List<Expr<BoolType>> ops = new ArrayList<>();
                for (int i = random.nextInt(4); i >= 0; i--) {
                    ops.add(randomExpr(random, vars, c, depth - 1));
                }
                return random.nextBoolean() ? And(ops) : Or(ops);
        }
    }

    /** Reference: joins the per-operand counts, which defines the expected result. */
    private static BasicVarIndexingBuilder joinOfOperands(final Expr<?> expr, final int nPrimes) {
        if (expr instanceof RefExpr<?> ref && ref.getDecl() instanceof VarDecl<?> varDecl) {
            return VarIndexingFactory.basicIndexingBuilder(0).inc(varDecl, nPrimes);
        }
        if (expr instanceof PrimeExpr<?> prime) {
            return joinOfOperands(prime.getOp(), nPrimes + 1);
        }
        BasicVarIndexingBuilder result = VarIndexingFactory.basicIndexingBuilder(0);
        for (final Expr<?> op : expr.getOps()) {
            result = result.join(joinOfOperands(op, nPrimes));
        }
        return result;
    }
}
