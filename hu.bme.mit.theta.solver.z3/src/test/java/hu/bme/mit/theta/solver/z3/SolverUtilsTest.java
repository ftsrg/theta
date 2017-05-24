package hu.bme.mit.theta.solver.z3;

import static hu.bme.mit.theta.core.decl.Decls.Const;
import static hu.bme.mit.theta.core.expr.Exprs.Gt;
import static hu.bme.mit.theta.core.type.impl.Types.Int;

import java.util.stream.Stream;

import org.junit.Test;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.model.Model;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.utils.SolverUtils;

public class SolverUtilsTest {

	@Test
	public void testModels() {
		// Arrange
		final SolverFactory factory = Z3SolverFactory.getInstace();

		final ConstDecl<IntType> cx = Const("x", Int());
		final ConstDecl<IntType> cy = Const("y", Int());
		final Expr<IntType> x = cx.getRef();
		final Expr<IntType> y = cy.getRef();
		final Expr<BoolType> expr = Gt(x, y);
		final Stream<Model> models = SolverUtils.models(factory, expr);

		// Act
		models.limit(5).forEach(System.out::println);
	}

}
