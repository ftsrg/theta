package hu.bme.mit.theta.core.utils;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Imply;
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

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.impl.Stmts;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.StmtUtils;

@RunWith(Parameterized.class)
public class VarCollectorStmtVisitorTest {
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
	public Stmt statement;

	@Parameter(value = 1)
	public Set<VarDecl<? extends Type>> expectedVars;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ Stmts.Skip(), of() },

				{ Stmts.Assign(va, d), of(va, vd) },

				{ Stmts.Assign(va, True()), of(va) },

				{ Stmts.Assert(And(Imply(a, d), Eq(c, Sub(b, e)))), of(va, vb, vc, vd, ve) },

				{ Stmts.Assume(Imply(a, d)), of(va, vd) },

				{ Stmts.Decl(va), of(va) },

				{ Stmts.Decl(va, d), of(va, vd) },

				{ Stmts.Do(Stmts.Assign(va, d), Eq(c, Sub(b, e))), of(va, vb, vc, vd, ve) },

				{ Stmts.Havoc(va), of(va) },

				{ Stmts.If(a, Stmts.Assign(vb, e)), of(va, vb, ve) },

				{ Stmts.If(a, Stmts.Assign(vb, e), Stmts.Assign(vc, e)), of(va, vb, vc, ve) },

				{ Stmts.Return(a), of(va) },

				{ Stmts.While(Eq(c, Sub(b, e)), Stmts.Assign(va, d)), of(va, vb, vc, vd, ve) },

				{ Stmts.Block(ImmutableList.of(Stmts.Assign(va, d), Stmts.Assign(vb, e))), of(va, vb, vd, ve) },

		});
	}

	@Test
	public void test() {
		final Set<VarDecl<? extends Type>> vars = StmtUtils.getVars(statement);
		assertEquals(expectedVars, vars);
	}
}
