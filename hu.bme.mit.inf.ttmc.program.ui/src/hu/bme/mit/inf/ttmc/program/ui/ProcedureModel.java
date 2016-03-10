package hu.bme.mit.inf.ttmc.program.ui;

import java.util.Collection;

import com.google.common.base.Optional;

import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;
import hu.bme.mit.inf.ttmc.formalism.decl.ProcDecl;
import hu.bme.mit.inf.ttmc.formalism.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.stmt.Stmt;

public interface ProcedureModel {
	public ProcDecl<? extends Type> getProcDecl();
	
	public Optional<Stmt> getStmt();
	
	public Collection<Expr<? extends BoolType>> getPreConds();
	public Collection<Expr<? extends BoolType>> getPostConds();
	public Collection<Expr<? extends BoolType>> getLoopInvars(Stmt stmt);
	
	public Collection<VarDecl<? extends Type>> getVarDecls();	
}