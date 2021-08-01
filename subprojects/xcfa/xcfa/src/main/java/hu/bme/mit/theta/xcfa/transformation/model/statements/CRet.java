package hu.bme.mit.theta.xcfa.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Map;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class CRet extends CStatement{
	private final CStatement expr;

	public CRet(CStatement expr) {
		this.expr = expr;
	}

	public CStatement getExpr() {
		return expr;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		if(expr == null) return lastLoc;
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		XcfaLocation endExpr = expr.build(builder, initLoc, breakLoc, continueLoc, returnLoc);
		XcfaLocation endLoc = new XcfaLocation("unreachable" + counter++, Map.of());
		builder.addLoc(endLoc);
        propagateMetadata(endLoc);
		VarDecl<?> key = builder.getParams().entrySet().iterator().next().getKey();
		XcfaEdge edge = new XcfaEdge(endExpr, returnLoc, List.of(Assign(cast(key, key.getType()), cast(expr.getExpression(), key.getType()))));
		builder.addEdge(edge);
        propagateMetadata(edge);
		return endLoc;
	}
}
