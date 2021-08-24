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
		XcfaLocation outerLastTest = new XcfaLocation("loc" + counter++, Map.of());
		builder.addLoc(endLoc);
        propagateMetadata(endLoc);
		builder.addLoc(outerLastTest);
        propagateMetadata(outerLastTest);
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
		XcfaLocation lastTest = guard.buildWithoutPostStatement(builder, lastInit, null, null, returnLoc);
		xcfaEdge = new XcfaEdge(lastTest, endInit, List.of(Assume(Neq(guard.getExpression(),  CComplexType.getType(guard.getExpression()).getNullValue()))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		xcfaEdge = new XcfaEdge(lastTest, outerLastTest, List.of(Assume(Eq(guard.getExpression(),  CComplexType.getType(guard.getExpression()).getNullValue()))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		XcfaLocation innerLastGuard = guard.buildPostStatement(builder, endInit, endLoc, startIncrement, returnLoc);
		XcfaLocation lastBody = body.build(builder, innerLastGuard, endLoc, startIncrement, returnLoc);
		xcfaEdge = new XcfaEdge(lastBody, startIncrement, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
        if(increment!=null) {
			XcfaLocation lastIncrement = increment.build(builder, startIncrement, null, null, returnLoc);
			xcfaEdge = new XcfaEdge(lastIncrement, lastInit, List.of());
			builder.addEdge(xcfaEdge);
			propagateMetadata(xcfaEdge);
		} else {
			xcfaEdge = new XcfaEdge(startIncrement, lastInit, List.of());
			builder.addEdge(xcfaEdge);
			propagateMetadata(xcfaEdge);
		}
		XcfaLocation outerLastGuard = guard.buildPostStatement(builder, outerLastTest, endLoc, startIncrement, returnLoc);
		xcfaEdge = new XcfaEdge(outerLastGuard, endLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(xcfaEdge);
		return endLoc;
	}
}
