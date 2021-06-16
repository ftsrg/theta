package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.xcfa.CIntTypeUtils;
import hu.bme.mit.theta.xcfa.model.XcfaEdge;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import hu.bme.mit.theta.xcfa.model.XcfaMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaProcedure;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;
import hu.bme.mit.theta.xcfa.transformation.c.types.CType;

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
		ret = Var("call_" + functionId + "_ret" + counter++, Int());
		CType paramType = CIntTypeUtils.getcTypeMetadata(functionId);
		XcfaMetadata.create(ret.getRef(), "cType", paramType);
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
		XcfaLocation initLoc = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(initLoc);
        propagateMetadata(initLoc);
		XcfaEdge xcfaEdge = new XcfaEdge(lastLoc, initLoc, List.of());
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		XcfaLocation location = getLoc() == null ? new XcfaLocation("loc" + counter++, Map.of()) : getLoc();
		builder.addLoc(location);
        propagateMetadata(location);
		List<Expr<?>> params = new ArrayList<>();
		params.add(ret.getRef());
		for (CStatement param : this.params) {
			initLoc = param.build(builder, initLoc, breakLoc, continueLoc, returnLoc);
		}
		params.addAll(this.params.stream().map(CStatement::getExpression).collect(Collectors.toList()));
		xcfaEdge = new XcfaEdge(initLoc, location, List.of(new XcfaCallStmt(params, functionId)));
		builder.addEdge(xcfaEdge);
        propagateMetadata(xcfaEdge);
		return location;
	}
}
