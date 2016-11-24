package hu.bme.mit.theta.core.utils;

import static com.google.common.collect.ImmutableSet.of;
import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.impl.Exprs.And;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Eq;
import static hu.bme.mit.theta.core.expr.impl.Exprs.False;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Int;
import static hu.bme.mit.theta.core.expr.impl.Exprs.Not;
import static hu.bme.mit.theta.core.expr.impl.Exprs.True;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static hu.bme.mit.theta.core.type.impl.Types.Int;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;
import java.util.Set;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.IndexedConstDecl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.IntType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.ExprUtils;

@RunWith(Parameterized.class)
public class IndexedConstDeclCollectorVisitorTest {
	private static final VarDecl<BoolType> VA = Var("a", Bool());
	private static final VarDecl<IntType> VB = Var("b", Int());

	private static final IndexedConstDecl<BoolType> A0 = VA.getConstDecl(0);
	private static final IndexedConstDecl<BoolType> A1 = VA.getConstDecl(1);
	private static final IndexedConstDecl<IntType> B0 = VB.getConstDecl(0);
	private static final IndexedConstDecl<IntType> B1 = VB.getConstDecl(1);

	@Parameter(value = 0)
	public Expr<? extends Type> expr;

	@Parameter(value = 1)
	public Set<IndexedConstDecl<? extends Type>> expectedConstDecls;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ And(True(), False(), Eq(Int(1), Int(2))), of() },

				{ And(A0.getRef(), Not(A1.getRef())), of(A0, A1) },

				{ And(A1.getRef(), A0.getRef(), Eq(B0.getRef(), B1.getRef())), of(A0, A1, B0, B1) },

		});

	}

	@Test
	public void test() {
		final Set<IndexedConstDecl<? extends Type>> actualConstDecls = ExprUtils.getIndexedConstDecls(expr);
		assertEquals(expectedConstDecls, actualConstDecls);
	}
}
