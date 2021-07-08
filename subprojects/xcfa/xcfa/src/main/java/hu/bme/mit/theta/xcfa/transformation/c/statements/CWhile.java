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

public class CWhile extends CStatement{

	//TODO: guard should not be multiple compounds inside!
	private final CStatement body;
	private final CStatement guard;

	public CWhile(CStatement body, CStatement guard) {
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
		builder.addLoc(initLoc);
		propagateMetadata(initLoc);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(xcfaEdge);
		XcfaLocation endLoc = new XcfaLocation("loc" + counter++, Map.of());
		builder.addLoc(endLoc);
		propagateMetadata(endLoc);
		XcfaLocation outerBeforeGuard = new XcfaLocation("loc" + counter++, Map.of());
		builder.addLoc(outerBeforeGuard);
		propagateMetadata(outerBeforeGuard);
		for(int i = 0; i < (UNROLL_COUNT == 0 ? 1 : UNROLL_COUNT); ++i) {
			if (((CCompound) body).getcStatementList().size() == 0) {
				xcfaEdge = new XcfaEdge(initLoc, endLoc, List.of(Assume(Neq(guard.getExpression(), Int(0)))));
				builder.addEdge(xcfaEdge);
				propagateMetadata(xcfaEdge);
				return endLoc;
			} else {
				XcfaLocation innerLoop = new XcfaLocation("loc" + counter++, Map.of());
				builder.addLoc(innerLoop);
				propagateMetadata(innerLoop);
				XcfaLocation testEndLoc = guard.buildWithoutPostStatement(builder, initLoc, null, null, returnLoc);
				if(UNROLL_COUNT > 0) {
					initLoc = new XcfaLocation("loc" + counter++, Map.of());
					builder.addLoc(initLoc);
					propagateMetadata(initLoc);
				}
				xcfaEdge = new XcfaEdge(testEndLoc, innerLoop, List.of(Assume(Neq(guard.getExpression(), Int(0)))));
				builder.addEdge(xcfaEdge);
				propagateMetadata(xcfaEdge);
				xcfaEdge = new XcfaEdge(testEndLoc, outerBeforeGuard, List.of(Assume(Eq(guard.getExpression(), Int(0)))));
				builder.addEdge(xcfaEdge);
				propagateMetadata(xcfaEdge);
				XcfaLocation lastGuard = guard.buildPostStatement(builder, innerLoop, endLoc, initLoc, returnLoc);
				XcfaLocation lastBody = body.build(builder, lastGuard, endLoc, initLoc, returnLoc);
				xcfaEdge = new XcfaEdge(lastBody, initLoc, List.of());
				builder.addEdge(xcfaEdge);
				propagateMetadata(xcfaEdge);
			}
		}
		XcfaLocation outerLastGuard = guard.buildPostStatement(builder, outerBeforeGuard, null, null, null);
		xcfaEdge = new XcfaEdge(outerLastGuard, endLoc, List.of());
		builder.addEdge(xcfaEdge);
		propagateMetadata(xcfaEdge);
		return endLoc;
	}
}
