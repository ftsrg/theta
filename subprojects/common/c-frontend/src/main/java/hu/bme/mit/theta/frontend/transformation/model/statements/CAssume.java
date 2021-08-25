package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;

import static com.google.common.base.Preconditions.checkNotNull;

public class CAssume extends CStatement{
	private final AssumeStmt assumeStmt;

	public CAssume(AssumeStmt assumeStmt) {
		checkNotNull(assumeStmt);
		this.assumeStmt = assumeStmt;
	}

	@Override
	public Expr<?> getExpression() {
		return assumeStmt.getCond();
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}

	public AssumeStmt getAssumeStmt() {
		return assumeStmt;
	}
}
