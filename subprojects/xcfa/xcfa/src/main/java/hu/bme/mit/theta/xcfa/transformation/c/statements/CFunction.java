package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;

public class CFunction extends CStatement{
	private final CDeclaration funcDecl;
	private final CStatement compound;

	public CFunction(CDeclaration funcDecl, CStatement compound) {
		this.funcDecl = funcDecl;
		this.compound = compound;
	}

	public CStatement getCompound() {
		return compound;
	}

	public CDeclaration getFuncDecl() {
		return funcDecl;
	}
}
