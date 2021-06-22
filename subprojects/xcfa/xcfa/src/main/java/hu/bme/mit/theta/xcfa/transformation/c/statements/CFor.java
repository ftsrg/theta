package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.stmt.Stmt;
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

public class CFor extends CStatement{
	private final CStatement body;
	private final CStatement init;
	private final CStatement guard;
	private final CStatement increment;

	public CFor(CStatement body, CStatement init, CStatement guard, CStatement increment) {
		this.body = body;
		this.init = init;
		this.guard = guard;
		this.increment = increment;
	}

	public CStatement getIncrement() {
		return increment;
	}

	public CStatement getGuard() {
		return guard;
	}

	public CStatement getInit() {
		return init;
	}

	public CStatement getBody() {
		return body;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		XcfaLocation endLoc = new XcfaLocation("loc" + counter++, Map.of());
		XcfaLocation endInit = new XcfaLocation("loc" + counter++, Map.of());
		XcfaLocation startIncrement = new XcfaLocation("loc" + counter++, Map.of());
		builder.addLoc(endLoc);
        propagateMetadata(endLoc);
		builder.addLoc(endInit);
        propagateMetadata(endInit);
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		builder.addLoc(startIncrement);
        propagateMetadata(startIncrement);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);

		XcfaLocation lastInit = init.build(builder, initLoc, null, null, returnLoc);
		XcfaLocation lastTest = guard.build(builder, lastInit, null, null, returnLoc);
		xcfaEdge = new XcfaEdge(lastTest, endInit, List.of(Assume(Neq(guard.getExpression(), Int(0)))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		xcfaEdge = new XcfaEdge(lastTest, endLoc, List.of(Assume(Eq(guard.getExpression(), Int(0)))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		XcfaLocation lastBody = body.build(builder, lastTest, endLoc, startIncrement, returnLoc);
		xcfaEdge = new XcfaEdge(lastBody, startIncrement, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		XcfaLocation lastIncrement = increment.build(builder, startIncrement, null, null, returnLoc);
		xcfaEdge = new XcfaEdge(lastIncrement, lastInit, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		return endLoc;
	}
}
