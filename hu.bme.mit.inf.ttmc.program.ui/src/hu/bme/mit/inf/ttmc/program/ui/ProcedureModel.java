package hu.bme.mit.inf.ttmc.program.ui;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFA;
import hu.bme.mit.inf.ttmc.formalism.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.formalism.decl.ProcDecl;

public interface ProcedureModel {
	public ProcDecl<? extends Type> getProcDecl();
	
	public Collection<Expr<? extends BoolType>> getPreConds();
	public Collection<Expr<? extends BoolType>> getPostConds();
	
	public Optional<CFA> getCFA();
	public Optional<Expr<? extends BoolType>> getAnnotation(CFALoc loc);
}