package hu.bme.mit.inf.theta.formalism.tests;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.False;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.inf.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Int;
import static hu.bme.mit.inf.theta.core.type.impl.Types.Rat;
import static hu.bme.mit.inf.theta.formalism.common.decl.impl.Decls2.Var;
import static org.junit.Assert.assertTrue;

import java.util.HashSet;
import java.util.Set;

import org.junit.Before;
import org.junit.Test;

import hu.bme.mit.inf.theta.core.expr.Expr;
import hu.bme.mit.inf.theta.core.type.BoolType;
import hu.bme.mit.inf.theta.core.type.IntType;
import hu.bme.mit.inf.theta.core.type.RatType;
import hu.bme.mit.inf.theta.core.type.Type;
import hu.bme.mit.inf.theta.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.theta.formalism.utils.FormalismUtils;

public class VarCollectorVisitorTests {

	VarDecl<BoolType> va;
	VarDecl<IntType> vb;
	VarDecl<RatType> vc;
	VarDecl<BoolType> vd;
	VarDecl<IntType> ve;

	Expr<BoolType> a;
	Expr<IntType> b;
	Expr<RatType> c;
	Expr<BoolType> d;
	Expr<IntType> e;

	@Before
	public void before() {
		va = Var("a", Bool());
		vb = Var("b", Int());
		vc = Var("c", Rat());
		vd = Var("d", Bool());
		ve = Var("e", Int());

		a = va.getRef();
		b = vb.getRef();
		c = vc.getRef();
		d = vd.getRef();
		e = ve.getRef();
	}

	@Test
	public void test() {
		assertTrue(checkExpr(And(True(), False(), Eq(Int(1), Int(2))), of()));

		assertTrue(checkExpr(And(a, Not(d)), of(va, vd)));

		assertTrue(checkExpr(And(Imply(a, d), Eq(c, Sub(b, e))), of(va, vb, vc, vd, ve)));
	}

	private boolean checkExpr(final Expr<? extends Type> expr, final Set<VarDecl<? extends Type>> expectedVars) {
		final Set<VarDecl<? extends Type>> vars = new HashSet<>();
		FormalismUtils.collectVars(expr, vars);
		return vars.equals(expectedVars);
	}

}
