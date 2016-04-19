package hu.bme.mit.inf.ttmc.formalism.tests;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.False;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.inf.ttmc.core.expr.impl.Exprs.True;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Int;
import static hu.bme.mit.inf.ttmc.core.type.impl.Types.Rat;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Var;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.IntType;
import hu.bme.mit.inf.ttmc.core.type.RatType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.utils.impl.FormalismUtils;

public class VarCollectorVisitorTests {

	VarDecl<BoolType> a;
	VarDecl<IntType> b;
	VarDecl<RatType> c;
	VarDecl<BoolType> d;
	VarDecl<IntType> e;

	@Before
	public void before() {
		a = Var("a", Bool());
		b = Var("b", Int());
		c = Var("c", Rat());
		d = Var("d", Bool());
		e = Var("e", Int());
	}

	@SuppressWarnings("serial")
	@Test
	public void test() {
		assertTrue(checkExpr(And(True(), False(), Eq(Int(1), Int(2))), new HashSet<VarDecl<? extends Type>>() {
			{
			}
		}));

		assertTrue(checkExpr(And(a.getRef(), Not(d.getRef())), of(a, d)));

		assertTrue(checkExpr(And(Imply(a.getRef(), d.getRef()), Eq(c.getRef(), Sub(b.getRef(), e.getRef()))),
				of(a, b, c, d, e)));
	}

	private boolean checkExpr(final Expr<? extends Type> expr, final Set<VarDecl<? extends Type>> expectedVars) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		FormalismUtils.collectVars(expr, vars);
		return vars.equals(expectedVars);
	}

}
