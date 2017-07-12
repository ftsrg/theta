package hu.bme.mit.theta.core.dsl;

import java.util.Arrays;
import java.util.Collection;

import org.junit.Assert;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.booltype.BoolExprs;
import hu.bme.mit.theta.core.type.inttype.IntExprs;
import hu.bme.mit.theta.core.type.inttype.IntType;

@RunWith(Parameterized.class)
public class StmtWriteTest {

	private static final VarDecl<IntType> VX = Decls.Var("x", IntExprs.Int());

	@Parameter(value = 0)
	public Stmt actual;

	@Parameter(value = 1)
	public String expected;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ Stmts.Havoc(VX), "havoc x" },

				{ Stmts.Assert(BoolExprs.True()), "assert true" },

				{ Stmts.Assume(BoolExprs.False()), "assume false" },

				{ Stmts.Assign(VX, IntExprs.Int(1)), "x := 1" },

		});
	}

	@Test
	public void test() {
		final CoreDslManager manager = new CoreDslManager();
		Assert.assertEquals(expected, manager.writeStmt(actual));
	}
}
