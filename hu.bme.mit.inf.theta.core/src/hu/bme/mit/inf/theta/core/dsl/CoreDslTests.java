package hu.bme.mit.inf.theta.core.dsl;

import static hu.bme.mit.inf.theta.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Bool;

import org.junit.Test;

import hu.bme.mit.inf.theta.core.decl.Decl;
import hu.bme.mit.inf.theta.core.expr.Expr;

public class CoreDslTests {

	@Test
	public void testExprParser() {
		final Decl<?, ?> x = Const("x", Bool());

		final CoreDslManager manager = new CoreDslManager();
		manager.declare(x);

		final Expr<?> expr = manager.parseExpr("(f : (int) -> int) -> (y : int) -> f(x) + f(y)");

		System.out.println(expr);
	}

}