package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CComplexType;
import hu.bme.mit.theta.frontend.transformation.model.types.complex.CVoid;

import java.util.List;
import java.util.Optional;

import static hu.bme.mit.theta.core.decl.Decls.Var;

public class CCall extends CStatement{
	private final VarDecl<?> ret;
	private final String functionId;
	private final List<CStatement> params;

	public CCall(String functionId, List<CStatement> params) {
		this.functionId = functionId;
		this.params = params;
		Optional<Object> cTypeOpt = FrontendMetadata.getMetadataValue(functionId, "cType");
		CComplexType type = (CComplexType) cTypeOpt.orElseGet(() -> new CVoid(null));
		ret = Var("call_" + functionId + "_ret" + counter++, type.getSmtType());
		FrontendMetadata.create(ret.getRef(), "cType", type);
	}

	public List<CStatement> getParams() {
		return params;
	}

	public VarDecl<?> getRet() {
		return ret;
	}

	public String getFunctionId() {
		return functionId;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
