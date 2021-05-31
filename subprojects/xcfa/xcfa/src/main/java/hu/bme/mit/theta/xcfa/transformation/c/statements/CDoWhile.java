package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Map;

import static hu.bme.mit.theta.core.stmt.Stmts.Assume;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Neq;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

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
		builder.addLoc(endLoc);
		builder.addLoc(innerEndLoc);
		builder.addLoc(initLoc);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		XcfaLocation lastBody = body.build(builder, initLoc, endLoc, innerEndLoc, returnLoc);
		xcfaEdge = new XcfaEdge(lastBody, innerEndLoc, List.of());
		builder.addEdge(xcfaEdge);
		XcfaLocation lastGuard = guard.build(builder, innerEndLoc, null, null, returnLoc);
		xcfaEdge = new XcfaEdge(lastGuard, initLoc, List.of(Assume(Neq(guard.getExpression(), Int(0)))));
		builder.addEdge(xcfaEdge);
		xcfaEdge = new XcfaEdge(lastGuard, endLoc, List.of(Assume(Eq(guard.getExpression(), Int(0)))));
		builder.addEdge(xcfaEdge);
		return endLoc;
	}
}
