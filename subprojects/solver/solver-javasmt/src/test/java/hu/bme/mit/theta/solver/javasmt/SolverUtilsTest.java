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
package hu.bme.mit.theta.solver.javasmt;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Gt;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.model.Valuation;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolLitExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.inttype.IntType;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.utils.SolverUtils;
import java.math.BigInteger;
import java.util.stream.Stream;
import org.junit.Assert;
import org.junit.Test;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.SolverContextFactory.Solvers;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaType;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.visitors.DefaultFormulaVisitor;

public class SolverUtilsTest {

    @Test
    public void testModels() {
        // Arrange
        final SolverFactory factory = JavaSMTSolverFactory.create(Solvers.Z3, new String[] {});

        final ConstDecl<IntType> cx = Const("x", Int());
        final ConstDecl<IntType> cy = Const("y", Int());
        final Expr<IntType> x = cx.getRef();
        final Expr<IntType> y = cy.getRef();
        final Expr<BoolType> expr = Gt(x, y);
        final Stream<Valuation> models = SolverUtils.models(factory, expr);

        // Act
        models.limit(5).forEach(m -> Assert.assertTrue(((BoolLitExpr) (expr.eval(m))).getValue()));
    }

    // https://github.com/sosy-lab/java-smt/issues/359
    // if this no longer fails, clean up the FpToFp mitigations in ExprTransformer
    @Test
    public void testBugreport() throws InvalidConfigurationException {
        final Configuration config = Configuration.fromCmdLineArguments(new String[] {});
        final LogManager logger = BasicLogManager.create(config);
        final ShutdownManager shutdownManager = ShutdownManager.create();
        final SolverContext context =
                SolverContextFactory.createSolverContext(
                        config, logger, shutdownManager.getNotifier(), Solvers.Z3);

        final Formula term =
                context.getFormulaManager()
                        .getFloatingPointFormulaManager()
                        .fromIeeeBitvector(
                                context.getFormulaManager()
                                        .getBitvectorFormulaManager()
                                        .makeBitvector(16, BigInteger.ZERO),
                                FormulaType.getFloatingPointType(5, 10));

        context.getFormulaManager()
                .visit(
                        term,
                        new DefaultFormulaVisitor<Void>() {
                            @Override
                            protected Void visitDefault(Formula f) {
                                return null;
                            }
                        });
    }
}
