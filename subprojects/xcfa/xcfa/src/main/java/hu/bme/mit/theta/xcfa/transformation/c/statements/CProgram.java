package hu.bme.mit.theta.xcfa.transformation.c.statements;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xcfa.transformation.c.declaration.CDeclaration;

import java.util.ArrayList;
import java.util.List;

public class CProgram extends CStatement{
	private final List<CFunction> functions;
	private final List<Tuple2<CDeclaration, VarDecl<?>>> globalDeclarations;

	public CProgram() {
		this.functions = new ArrayList<>();
		this.globalDeclarations = new ArrayList<>();
	}

	public List<Tuple2<CDeclaration, VarDecl<?>>> getGlobalDeclarations() {
		return globalDeclarations;
	}

	public List<CFunction> getFunctions() {
		return functions;
	}
}
