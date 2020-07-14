package hu.bme.mit.theta.xcfa.tocfa.utils;

import java.util.Collection;
import java.util.Map;
import java.util.Optional;

import com.google.common.base.Preconditions;

import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.model.Substitution;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

public class VarMapperStmtVisitor implements StmtVisitor<Map<VarDecl<?>, VarDecl<?>>, Stmt> {
	
	@Override
	public Stmt visit(SkipStmt stmt, Map<VarDecl<?>, VarDecl<?>> param) {
		return stmt;
	}

	@Override
	public Stmt visit(AssumeStmt stmt, Map<VarDecl<?>, VarDecl<?>> param) {
		return Stmts.Assume(new VarSubstitution(param).apply(stmt.getCond()));
	}
	
	@Override
	public <DeclType extends Type> Stmt visit(AssignStmt<DeclType> stmt, Map<VarDecl<?>, VarDecl<?>> param) {
		var expr = new VarSubstitution(param).apply(stmt.getExpr());
		var vari = param.getOrDefault(stmt.getVarDecl(), stmt.getVarDecl());
		return Stmts.Assign(unsafeCast(vari, expr.getType()), expr);
	}

	@Override
	public <DeclType extends Type> Stmt visit(HavocStmt<DeclType> stmt, Map<VarDecl<?>, VarDecl<?>> param) {
		var vari = param.getOrDefault(stmt.getVarDecl(), stmt.getVarDecl());
		return Stmts.Havoc(vari);
	}

	@Override
	public Stmt visit(XcfaStmt xcfaStmt, Map<VarDecl<?>, VarDecl<?>> param) {
		// TODO ugly
		Preconditions.checkState(false, "Xcfa stmt mapping not implemented");
		return null;
	}
	
	private static class LazyHolder {
		private static final VarMapperStmtVisitor INSTANCE = new VarMapperStmtVisitor();
	}
	
	public static VarMapperStmtVisitor getInstance() {
		return LazyHolder.INSTANCE;
	}
	
	private class VarSubstitution implements Substitution{
		private final Map<VarDecl<?>, VarDecl<?>> varMapping;
		public VarSubstitution(Map<VarDecl<?>, VarDecl<?>> varMapping) {
			this.varMapping = varMapping;
		}
		
		@Override
		public Collection<? extends Decl<?>> getDecls() {
			return varMapping.keySet();
		}
		
		@Override
		public <DeclType extends Type> Optional<? extends Expr<DeclType>> eval(Decl<DeclType> decl) {
			if (decl instanceof VarDecl) {
				var v = (VarDecl<DeclType>)varMapping.get((VarDecl<DeclType>)decl);
				return Optional.ofNullable(v).map(t -> t.getRef());
			}
			return Optional.empty();
		}
	}

	<T extends Type> VarDecl<T> unsafeCast(VarDecl<?> a, final T type) {
		return (VarDecl<T>)a;
	}

}
