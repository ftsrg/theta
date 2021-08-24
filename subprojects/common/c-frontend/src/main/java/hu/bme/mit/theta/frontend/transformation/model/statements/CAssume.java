package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.Collections;
import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Add;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Mul;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

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
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		XcfaLocation location = new XcfaLocation("loc" + counter++, Map.of());
		builder.addLoc(location);
        propagateMetadata(location);

		xcfaEdge = new XcfaEdge(initLoc, location, Collections.singletonList(assumeStmt)); // List.of(Assign(cast((VarDecl<?>)((RefExpr<?>) lValue).getDecl(), Int()), cast(getrExpression(), Int()))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		return location;
	}
}
