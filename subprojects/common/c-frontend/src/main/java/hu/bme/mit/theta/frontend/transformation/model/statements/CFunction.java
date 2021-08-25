package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.frontend.transformation.model.declaration.CDeclaration;

import java.util.List;

public class CFunction extends CStatement{
	private final CDeclaration funcDecl;
	private final CStatement compound;
	private final List<VarDecl<?>> flatVariables;

	public CFunction(CDeclaration funcDecl, CStatement compound, List<VarDecl<?>> flatVariables) {
		this.funcDecl = funcDecl;
		this.compound = compound;
		this.flatVariables = flatVariables;
		FrontendMetadata.lookupMetadata(funcDecl).forEach((s, o) -> FrontendMetadata.create(this, s, o));
	}

	public CStatement getCompound() {
		return compound;
	}

	public CDeclaration getFuncDecl() {
		return funcDecl;
	}

	public List<VarDecl<?>> getFlatVariables() {
		return flatVariables;
	}

	@Override
	public <P, R> R accept(CStatementVisitor<P, R> visitor, P param) {
		return visitor.visit(this, param);
	}
}
