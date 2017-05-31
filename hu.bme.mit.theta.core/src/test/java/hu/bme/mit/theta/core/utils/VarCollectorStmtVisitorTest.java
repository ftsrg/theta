package hu.bme.mit.theta.core.utils;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.expr.Exprs.Eq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Imply;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static hu.bme.mit.theta.core.type.impl.Types.Rat;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Sub;
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
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.RatType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.StmtUtils;

@RunWith(Parameterized.class)
public class VarCollectorStmtVisitorTest {
	private static final VarDecl<BoolType> VA = Var("a", Bool());
	private static final VarDecl<IntType> VB = Var("b", Int());
	private static final VarDecl<RatType> VC = Var("c", Rat());
	private static final VarDecl<BoolType> VD = Var("d", Bool());
	private static final VarDecl<IntType> VE = Var("e", Int());
	private static final VarDecl<RatType> VF = Var("f", Rat());

	private static final Expr<BoolType> A = VA.getRef();
	private static final Expr<IntType> B = VB.getRef();
	private static final Expr<RatType> C = VC.getRef();
	private static final Expr<BoolType> D = VD.getRef();
	private static final Expr<IntType> E = VE.getRef();
	private static final Expr<RatType> F = VF.getRef();

	@Parameter(value = 0)
	public Stmt statement;

	@Parameter(value = 1)
	public Set<VarDecl<? extends Type>> expectedVars;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ Stmts.Skip(), of() },

				{ Stmts.Assign(VA, D), of(VA, VD) },

				{ Stmts.Assign(VA, True()), of(VA) },

				{ Stmts.Assert(And(Imply(A, D), Eq(C, Sub(B, E)))), of(VA, VB, VC, VD, VE) },

				{ Stmts.Assume(Imply(A, D)), of(VA, VD) },

				{ Stmts.Decl(VA), of(VA) },

				{ Stmts.Decl(VA, D), of(VA, VD) },

				{ Stmts.Do(Stmts.Assign(VA, D), Eq(C, Sub(B, E))), of(VA, VB, VC, VD, VE) },

				{ Stmts.Havoc(VA), of(VA) },

				{ Stmts.If(A, Stmts.Assign(VB, E)), of(VA, VB, VE) },

				{ Stmts.If(A, Stmts.Assign(VB, E), Stmts.Assign(VC, F)), of(VA, VB, VC, VE, VF) },

				{ Stmts.Return(A), of(VA) },

				{ Stmts.While(Eq(C, Sub(B, E)), Stmts.Assign(VA, D)), of(VA, VB, VC, VD, VE) },

				{ Stmts.Block(ImmutableList.of(Stmts.Assign(VA, D), Stmts.Assign(VB, E))), of(VA, VB, VD, VE) },

		});
	}

	@Test
	public void test() {
		final Set<VarDecl<? extends Type>> vars = StmtUtils.getVars(statement);
		assertEquals(expectedVars, vars);
	}
}
