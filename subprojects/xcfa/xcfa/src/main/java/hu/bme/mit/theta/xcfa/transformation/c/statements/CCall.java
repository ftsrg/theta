package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.decl.Decls.Var;
import static hu.bme.mit.theta.core.type.inttype.IntExprs.Int;

public class CCall extends CStatement{
	private final VarDecl<?> ret;
	private final String functionId;
	private final List<CStatement> params;

	public CCall(String functionId, List<CStatement> params) {
		this.functionId = functionId;
		this.params = params;
		ret = Var("functionret", Int());
	}

	public String getId() {
		return functionId;
	}

	public List<CStatement> getParams() {
		return params;
	}

	public VarDecl<?> getRet() {
		return ret;
	}

	@Override
	public XcfaLocation build(XcfaProcedure.Builder builder, XcfaLocation lastLoc, XcfaLocation breakLoc, XcfaLocation continueLoc, XcfaLocation returnLoc) {
		XcfaLocation location = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(location);
		List<Expr<?>> params = new ArrayList<>();
		params.add(ret.getRef());
		for (CStatement param : this.params) {
			lastLoc = param.build(builder, lastLoc, breakLoc, continueLoc, returnLoc);
		}
		params.addAll(this.params.stream().map(CStatement::getExpression).collect(Collectors.toList()));
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, location, List.of(new XcfaCallStmt(params, functionId)));
		builder.addEdge(xcfaEdge);
		return location;
	}
}
