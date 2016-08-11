package hu.bme.mit.inf.ttmc.core.dsl;

import static hu.bme.mit.inf.ttmc.core.decl.impl.Decls.Const;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;

import org.junit.Test;

import hu.bme.mit.inf.ttmc.common.dsl.GlobalScope;
import hu.bme.mit.inf.ttmc.common.dsl.Scope;
import hu.bme.mit.inf.ttmc.core.decl.Decl;
import hu.bme.mit.inf.ttmc.core.expr.Expr;

public class CoreDSLTests {

	@Test
	public void testExprParser() {
		final Decl<?, ?> x = Const("x", Bool());

		final Scope scope = new GlobalScope();
		scope.declare(new DeclSymbol(x));

		final Expr<?> expr = CoreDSL.parseExpr(scope, "(f : (int) -> int) -> (y : int) -> f(x) + f(y)");

		System.out.println(expr);
	}

}