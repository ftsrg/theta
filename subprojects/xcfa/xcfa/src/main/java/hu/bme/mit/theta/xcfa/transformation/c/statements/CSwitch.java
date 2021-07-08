package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

public class CSwitch extends CStatement{
	private final CStatement testValue;
	private final CStatement body;

	public CSwitch(CStatement testValue, CStatement body) {
		this.testValue = testValue;
		this.body = body;
	}

	public CStatement getBody() {
		return body;
	}

	public CStatement getTestValue() {
		return testValue;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaLocation endLoc = new XcfaLocation("loc" + counter++, Map.of());
		builder.addLoc(endLoc);
        propagateMetadata(endLoc);
		XcfaEdge edge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(edge);
        propagateMetadata(edge);
		XcfaLocation endInit = testValue.buildWithoutPostStatement(builder, initLoc, breakLoc, continueLoc, returnLoc);
		checkState(body instanceof CCompound, "Switch body has to be a CompoundStatement!");
		Expr<BoolType> defaultExpr = True();
		for (CStatement statement : ((CCompound) body).getcStatementList()) {
			if(statement instanceof CCase) {
				defaultExpr = And(defaultExpr, Neq(testValue.getExpression(), ((CCase) statement).getExpr().getExpression()));
			}
		}
		XcfaLocation lastLocation = null;
		for (CStatement statement : ((CCompound) body).getcStatementList()) {
			XcfaLocation location = new XcfaLocation("loc" + counter++, Map.of());
			builder.addLoc(location);
        propagateMetadata(location);
			XcfaEdge xcfaEdge;
			if(lastLocation != null) {
				xcfaEdge = new XcfaEdge(lastLocation, location, List.of());
				builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
			}
			if(statement instanceof CCase) {
				XcfaLocation afterGuard = testValue.buildPostStatement(builder, endInit, breakLoc, continueLoc, returnLoc);
				xcfaEdge = new XcfaEdge(afterGuard, location, List.of(Assume(Eq(testValue.getExpression(), ((CCase) statement).getExpr().getExpression()))));
				builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
			} else if(statement instanceof CDefault) {
				XcfaLocation afterGuard = testValue.buildPostStatement(builder, endInit, breakLoc, continueLoc, returnLoc);
				xcfaEdge = new XcfaEdge(afterGuard, location, List.of(Assume(defaultExpr)));
				builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
			}
			lastLocation = statement.build(builder, location, endLoc, continueLoc, returnLoc);
		}
		if(lastLocation != null) {
			XcfaEdge xcfaEdge = new XcfaEdge(lastLocation, endLoc, List.of());
			builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		}
		return endLoc;
	}
}
