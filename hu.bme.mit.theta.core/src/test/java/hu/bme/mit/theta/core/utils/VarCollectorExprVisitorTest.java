package hu.bme.mit.theta.core.utils;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.False;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Imply;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Sub;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static hu.bme.mit.theta.core.type.impl.Types.Rat;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

@RunWith(Parameterized.class)
public class VarCollectorExprVisitorTest {

	private static final VarDecl<BoolType> va = Var("a", Bool());
	private static final VarDecl<IntType> vb = Var("b", Int());
	private static final VarDecl<RatType> vc = Var("c", Rat());
	private static final VarDecl<BoolType> vd = Var("d", Bool());
	private static final VarDecl<IntType> ve = Var("e", Int());

	private static final Expr<BoolType> a = va.getRef();
	private static final Expr<IntType> b = vb.getRef();
	private static final Expr<RatType> c = vc.getRef();
	private static final Expr<BoolType> d = vd.getRef();
	private static final Expr<IntType> e = ve.getRef();

	@Parameter(value = 0)
	public Expr<? extends Type> expr;

	@Parameter(value = 1)
	public Set<VarDecl<? extends Type>> expectedVars;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ And(True(), False(), Eq(Int(1), Int(2))), of() },

				{ And(a, Not(d)), of(va, vd) },

				{ And(Imply(a, d), Eq(c, Sub(b, e))), of(va, vb, vc, vd, ve) }, });
	}

	@Test
	public void test() {
		final Set<VarDecl<? extends Type>> vars = ExprUtils.getVars(expr);
		assertEquals(expectedVars, vars);
	}

}
