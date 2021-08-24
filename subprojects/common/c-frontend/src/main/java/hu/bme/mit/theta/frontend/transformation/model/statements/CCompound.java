package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

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
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaEdge edge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
        propagateMetadata(edge);
		lastLoc = initLoc;
		if(preStatements != null) lastLoc = preStatements.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		for (CStatement statement : cStatementList) {
			if(statement != null) lastLoc = statement.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		}
		if(postStatements != null) lastLoc = postStatements.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		return lastLoc;
	}

	@Override
	public XcfaLocation buildWithoutPostStatement(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
		propagateMetadata(initLoc);
		XcfaEdge edge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
		propagateMetadata(edge);
		lastLoc = initLoc;
		if(preStatements != null) lastLoc = preStatements.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		for (int i = 0; i < cStatementList.size()-1; i++) {
			CStatement statement = cStatementList.get(i);
			if (statement != null) lastLoc = statement.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		}
		CStatement lastStatement = this.cStatementList.get(cStatementList.size() - 1);
		if(this.postStatements == null) {
			lastLoc = lastStatement.buildWithoutPostStatement(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		} else {
			lastLoc = lastStatement.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		}
		return lastLoc;
	}

	@Override
	public XcfaLocation buildPostStatement(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		if(postStatements != null) lastLoc = postStatements.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		else lastLoc = cStatementList.get(cStatementList.size()-1).buildPostStatement(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		return lastLoc;
	}

}
