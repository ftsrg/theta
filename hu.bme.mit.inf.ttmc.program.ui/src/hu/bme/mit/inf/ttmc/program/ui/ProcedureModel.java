package hu.bme.mit.inf.ttmc.program.ui;

import java.util.Collection;
import java.util.Optional;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.program.cfa.CFA;
import hu.bme.mit.inf.ttmc.program.cfa.CFALoc;
import hu.bme.mit.inf.ttmc.program.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.program.stmt.Stmt;

public interface ProcedureModel {
	public ProcDecl<? extends Type> getProcDecl();
	
	public Collection<Expr<? extends BoolType>> getPreConds();
	public Collection<Expr<? extends BoolType>> getPostConds();
	
	public Optional<Stmt> getStmt();
	public Optional<CFA> getCFA();
	public Optional<Expr<? extends BoolType>> getAnnotation(Stmt stmt);
	public Optional<Expr<? extends BoolType>> getAnnotation(CFALoc loc);
}