package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;

import java.util.List;
import java.util.Map;

import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;

public class CDoWhile extends CStatement{
	private final CStatement body;
	private final CStatement guard;

	public CDoWhile(CStatement body, CStatement guard) {
		this.body = body;
		this.guard = guard;
	}

	public CStatement getBody() {
		return body;
	}

	public CStatement getGuard() {
		return guard;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		XcfaLocation endLoc = new XcfaLocation("loc" + counter++, Map.of());
		XcfaLocation innerEndLoc = new XcfaLocation("loc" + counter++, Map.of());
		XcfaLocation innerInnerGuard = new XcfaLocation("loc" + counter++, Map.of());
		XcfaLocation outerInnerGuard = new XcfaLocation("loc" + counter++, Map.of());
		builder.addLoc(endLoc);
        propagateMetadata(endLoc);
		builder.addLoc(innerInnerGuard);
        propagateMetadata(innerInnerGuard);
		builder.addLoc(outerInnerGuard);
        propagateMetadata(outerInnerGuard);
		builder.addLoc(innerEndLoc);
        propagateMetadata(innerEndLoc);
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		XcfaLocation lastBody = body.build(builder, initLoc, endLoc, innerEndLoc, returnLoc);
		xcfaEdge = new XcfaEdge(lastBody, innerEndLoc, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		XcfaLocation lastPre = guard.buildWithoutPostStatement(builder, innerEndLoc, null, null, returnLoc);
		xcfaEdge = new XcfaEdge(lastPre, innerInnerGuard, List.of(Assume(Neq(guard.getExpression(), CComplexType.getType(guard.getExpression()).getNullValue()))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		xcfaEdge = new XcfaEdge(lastPre, outerInnerGuard, List.of(Assume(Eq(guard.getExpression(),  CComplexType.getType(guard.getExpression()).getNullValue()))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
        XcfaLocation outerLastGuard = guard.buildPostStatement(builder, outerInnerGuard, null, null, null);
        XcfaLocation innerLastGuard = guard.buildPostStatement(builder, innerInnerGuard, null, null, null);
		xcfaEdge = new XcfaEdge(outerLastGuard, endLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(xcfaEdge);
		xcfaEdge = new XcfaEdge(innerLastGuard, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(xcfaEdge);
        return endLoc;
	}
}
