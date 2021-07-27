package hu.bme.mit.theta.xcfa.transformation.model.statements;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.transformation.model.declaration.CDeclaration;

import java.util.ArrayList;
import java.util.List;

public class CDecls extends CStatement{
	private final List<Tuple2<CDeclaration, VarDecl<?>>> cDeclarations;

	public CDecls() {
		this.cDeclarations = new ArrayList<>();
	}

	public List<Tuple2<CDeclaration, VarDecl<?>>> getcDeclarations() {
		return cDeclarations;
	}

	@Override
	public Object build(Object param) {
		throw new RuntimeException("Cannot build CDecls!");
	}
}
