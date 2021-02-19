package hu.bme.mit.theta.xsts.dsl;

import hu.bme.mit.theta.common.dsl.DynamicScope;
import hu.bme.mit.theta.common.dsl.Env;
import hu.bme.mit.theta.common.dsl.Scope;
import hu.bme.mit.theta.common.dsl.SymbolTable;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslBaseVisitor;
import hu.bme.mit.theta.xsts.dsl.gen.XstsDslParser.TransitionSetContext;

import java.util.List;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public class XstsTransitionSet {

	private final DynamicScope scope;
	private final SymbolTable typeTable;
	private final TransitionSetContext context;

	public XstsTransitionSet(final DynamicScope scope, final SymbolTable typeTable, final TransitionSetContext context) {
		this.scope = checkNotNull(scope);
		this.typeTable = checkNotNull(typeTable);
		this.context = checkNotNull(context);
	}

	public NonDetStmt instantiate(final Env env) {
		final TransitionSetCreatorVisitor visitor = new TransitionSetCreatorVisitor(env);
		final NonDetStmt stmt = context.accept(visitor);
		if (stmt == null) {
			throw new AssertionError();
		} else {
			return stmt;
		}
	}

	private final class TransitionSetCreatorVisitor extends XstsDslBaseVisitor<NonDetStmt> {

		private final Env env;

		public TransitionSetCreatorVisitor(final Env env) {
			this.env = checkNotNull(env);
		}

		@Override
		public NonDetStmt visitTransitionSet(TransitionSetContext ctx) {
			final List<Stmt> stmts = ctx.stmts.stream()
					.map((stmtContext -> new XstsStatement(scope,typeTable,stmtContext).instantiate(env))).collect(Collectors.toList());
			return NonDetStmt.of(stmts);
		}
	}

}
