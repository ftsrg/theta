package hu.bme.mit.theta.formalism.cfa.dsl;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.stream.Collectors.toList;

import java.util.ArrayList;
import java.util.List;

import hu.bme.mit.theta.common.dsl.Environment;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.formalism.cfa.CFA;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaEdge;
import hu.bme.mit.theta.formalism.cfa.CFA.CfaLoc;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.EdgeContext;
import hu.bme.mit.theta.formalism.cfa.dsl.gen.CfaDslParser.StmtContext;

final class CfaEdgeDefinition {

	private final CfaProcessSymbol scope;

	private final String source;
	private final String target;
	private final List<CfaStatement> statements;

	public CfaEdgeDefinition(final CfaProcessSymbol scope, final EdgeContext context) {
		checkNotNull(context);
		this.scope = checkNotNull(scope);

		source = context.source.getText();
		target = context.target.getText();
		statements = createStatements(context.stmts);
	}

	////

	public CfaEdge instantiate(final CFA cfa, final Environment env) {
		final CfaLocationSymbol sourceSymbol = (CfaLocationSymbol) scope.resolve(source).get();
		final CfaLocationSymbol targetSymbol = (CfaLocationSymbol) scope.resolve(target).get();

		final CfaLoc sourceLoc = (CfaLoc) env.eval(sourceSymbol);
		final CfaLoc targetLoc = (CfaLoc) env.eval(targetSymbol);

		final CfaEdge edge = cfa.createEdge(sourceLoc, targetLoc);

		final List<Stmt> stmts = statements.stream().map(s -> s.instantiate(env)).collect(toList());
		edge.getStmts().addAll(stmts);

		return edge;
	}

	////

	private List<CfaStatement> createStatements(final List<StmtContext> stmtContexts) {
		final List<CfaStatement> result = new ArrayList<>();
		for (final StmtContext stmtContext : stmtContexts) {
			final CfaStatement statement = new CfaStatement(scope, stmtContext);
			result.add(statement);
		}
		return result;
	}

}
