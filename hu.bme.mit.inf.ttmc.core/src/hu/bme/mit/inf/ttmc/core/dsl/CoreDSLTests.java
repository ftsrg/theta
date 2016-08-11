package hu.bme.mit.inf.ttmc.core.dsl;

import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;

public class CoreDSLTests {

	@Test
	public void testExprParser() {
		final Decl<?, ?> x = Const("x", Bool());

		final CoreDSL manager = new CoreDSL();
		manager.declare(x);

		final Expr<?> expr = manager.parseExpr("(f : (int) -> int) -> (y : int) -> f(x) + f(y)");

		System.out.println(expr);
	}

}