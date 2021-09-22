package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;

import java.util.ArrayList;
import java.util.List;

public class CCompound extends CStatement{
	private final List<CStatement> cStatementList;

	public CCompound() {
		cStatementList = new ArrayList<>();
	}

	public List<CStatement> getcStatementList() {
		return cStatementList;
	}

	@Override
	public Expr<?> getExpression() {
		return cStatementList.get(cStatementList.size() - 1).getExpression();
	}

	@Override
	public void setPostStatements(CStatement postStatements) {
		this.postStatements = postStatements;
	}

	@Override
	public void setPreStatements(CStatement preStatements) {
		this.preStatements = preStatements;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}

}
