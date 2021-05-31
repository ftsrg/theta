package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class CAssignment extends CStatement{
	private final Expr<?> lValue;
	private final CStatement rValue;

	public CAssignment(Expr<?> lValue, CStatement rValue) {
		this.lValue = lValue;
		this.rValue = rValue;
	}

	public CStatement getrValue() {
		return rValue;
	}

	public Expr<?> getlValue() {
		return lValue;
	}

	@Override
	public Expr<?> getExpression() {
		return rValue.getExpression();
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation location = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(location);
		checkState(lValue instanceof RefExpr && ((RefExpr<?>) lValue).getDecl() instanceof VarDecl<?>, "lValue must be a variable!");
		lastLoc = rValue.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, location, List.of(Assign(cast((VarDecl<?>)((RefExpr<?>) lValue).getDecl(), Int()), cast(rValue.getExpression(), Int()))));
		builder.addEdge(xcfaEdge);
		return location;
	}
}
