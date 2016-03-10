package hu.bme.mit.inf.ttmc.constraint.z3.decl;


import com.microsoft.z3.FuncDecl;

import hu.bme.mit.inf.ttmc.constraint.solver.impl.WrapperDecl;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

public interface Z3Decl<DeclType extends Type> extends WrapperDecl<DeclType, FuncDecl> {
	
}
