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

public class CIf extends CStatement{
	private final CStatement guard;
	private final CStatement body;
	private final CStatement elseStatement;

	public CIf(CStatement guard, CStatement body, CStatement elseStatement) {
		this.guard = guard;
		this.body = body;
		this.elseStatement = elseStatement;
	}

	public CStatement getElseStatement() {
		return elseStatement;
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
		XcfaLocation mainBranch = new XcfaLocation("loc" + counter++, Map.of());
		XcfaLocation elseBranch = new XcfaLocation("loc" + counter++, Map.of());
		builder.addLoc(endLoc);
        propagateMetadata(endLoc);
		builder.addLoc(mainBranch);
        propagateMetadata(mainBranch);
		builder.addLoc(elseBranch);
        propagateMetadata(elseBranch);
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		XcfaLocation endGuard = guard.build(builder, initLoc, breakLoc, continueLoc, returnLoc);
		xcfaEdge = new XcfaEdge(endGuard, mainBranch, List.of(Assume(Neq(guard.getExpression(), Int(0)))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		xcfaEdge = new XcfaEdge(endGuard, elseBranch, List.of(Assume(Eq(guard.getExpression(), Int(0)))));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);

		XcfaLocation mainEnd = body.build(builder, mainBranch, breakLoc, continueLoc, returnLoc);
		if(elseStatement != null) {
			XcfaLocation elseEnd = elseStatement.build(builder, elseBranch, breakLoc, continueLoc, returnLoc);
			xcfaEdge = new XcfaEdge(elseEnd, endLoc, List.of());
			builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		} else {
			xcfaEdge = new XcfaEdge(elseBranch, endLoc, List.of());
			builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		}

		xcfaEdge = new XcfaEdge(mainEnd, endLoc, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		return endLoc;
	}
}
