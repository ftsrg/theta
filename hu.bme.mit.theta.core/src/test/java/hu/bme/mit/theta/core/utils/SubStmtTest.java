package hu.bme.mit.theta.core.utils;

import static com.google.common.collect.ImmutableList.of;
import static hu.bme.mit.theta.core.decl.impl.Decls.Var;
import static hu.bme.mit.theta.core.expr.Exprs.True;
import static hu.bme.mit.theta.core.stmt.impl.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.impl.Stmts.Block;
import static hu.bme.mit.theta.core.stmt.impl.Stmts.Havoc;
import static hu.bme.mit.theta.core.stmt.impl.Stmts.Skip;
import static hu.bme.mit.theta.core.type.impl.Types.Bool;
import static org.junit.Assert.assertEquals;

import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameter;
import org.junit.runners.Parameterized.Parameters;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.utils.impl.StmtUtils;

@RunWith(Parameterized.class)
public class SubStmtTest {

	private static final VarDecl<BoolType> VA = Var("a", Bool());

	@Parameter(value = 0)
	public Stmt statement;

	@Parameter(value = 1)
	public List<? extends Stmt> expectedSubStmts;

	@Parameters
	public static Collection<Object[]> data() {
		return Arrays.asList(new Object[][] {

				{ Skip(), of(Skip()) },

				{ Havoc(VA), of(Havoc(VA)) },

				{ Block(of(Skip(), Havoc(VA))), of(Skip(), Havoc(VA)) },

				{ Block(of(Skip(), Block(of(Havoc(VA), Assign(VA, True()))))),
						of(Skip(), Havoc(VA), Assign(VA, True())) },

		});
	}

	@Test
	public void test() {
		final List<? extends Stmt> subStmts = StmtUtils.getSubStmts(statement);
		assertEquals(expectedSubStmts, subStmts);
	}
}
