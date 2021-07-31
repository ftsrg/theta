package hu.bme.mit.theta.xcfa.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.abstracttype.AbstractExprs;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.transformation.model.types.complex.CComplexType;

import java.util.List;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;
import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class CAssignment extends CStatement{
	private final Expr<?> lValue;
	private final CStatement rValue;
	private final String operator;

	public CAssignment(Expr<?> lValue, CStatement rValue, String operator) {
		checkNotNull(rValue.getExpression());
		this.lValue = lValue;
		this.rValue = rValue;
		this.operator = operator;
	}

	public CStatement getrValue() {
		return rValue;
	}

	public Expr<?> getlValue() {
		return lValue;
	}

	@Override
	public Expr<?> getExpression() {
		return lValue;
	}

	public Expr<?> getrExpression() {
		Expr<?> ret = null;
		switch (operator) {
			case "=": return rValue.getExpression();
			case "*=": ret = AbstractExprs.Mul(lValue, rValue.getExpression()); break;
			case "/=": ret = AbstractExprs.Div(lValue, rValue.getExpression()); break;
			case "%=": ret = AbstractExprs.Mod(lValue, rValue.getExpression()); break;
			case "+=": ret = AbstractExprs.Add(lValue, rValue.getExpression()); break;
			case "-=": ret = AbstractExprs.Sub(lValue, rValue.getExpression()); break;
			default: throw new RuntimeException("Bad operator!");
		}
		XcfaMetadata.create(ret, "cType", CComplexType.getType(lValue));
		ret = CComplexType.getType(ret).castTo(ret);
		return ret;
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
		checkState(lValue instanceof RefExpr && ((RefExpr<?>) lValue).getDecl() instanceof VarDecl<?>, "lValue must be a variable!");
		initLoc = rValue.build(builder, initLoc, breakLoc, continueLoc, returnLoc);
		xcfaEdge = new XcfaEdge(initLoc, location, List.of(Assign(cast((VarDecl<?>)((RefExpr<?>) lValue).getDecl(), ((VarDecl<?>)((RefExpr<?>) lValue).getDecl()).getType()), cast(getrExpression(), ((VarDecl<?>)((RefExpr<?>) lValue).getDecl()).getType()))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		return location;
	}
}
