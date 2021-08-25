package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.LoopStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.OrtStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.stmt.XcfaStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicBeginStmt;
import hu.bme.mit.theta.core.stmt.xcfa.AtomicEndStmt;
import hu.bme.mit.theta.core.stmt.xcfa.FenceStmt;
import hu.bme.mit.theta.core.stmt.xcfa.JoinThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.LoadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StartThreadStmt;
import hu.bme.mit.theta.core.stmt.xcfa.StoreStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaCallStmt;
import hu.bme.mit.theta.core.stmt.xcfa.XcfaStmtVisitor;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;

public class StmtVarToArrayItemVisitor<P extends Type> implements XcfaStmtVisitor<Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>>, List<Stmt>> {

	private Optional<Expr<Type>> getTypeExpr(Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param, Expr<Type> expr) {
		if (expr instanceof RefExpr && param.containsKey(((RefExpr<Type>) expr).getDecl())) {
			Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>> replacement = param.get(((RefExpr<Type>) expr).getDecl());
			return Optional.of(cast(ArrayReadExpr.of(cast(replacement.get1().getRef(), replacement.get1().getType()), replacement.get2()), expr.getType()));
		}
		return Optional.empty();
	}


	@Override
	public List<Stmt> visit(SkipStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(stmt);
	}

	@Override
	public List<Stmt> visit(AssumeStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		Optional<Expr<BoolType>> newExpr = ExpressionReplacer.replace(stmt.getCond(), expr -> getTypeExpr(param, expr));
		return List.of(newExpr.map(Stmts::Assume).orElse(stmt));
	}

	@Override
	public <DeclType extends Type> List<Stmt> visit(AssignStmt<DeclType> stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		Optional<Expr<DeclType>> declTypeExpr = ExpressionReplacer.replace(stmt.getExpr(), expr -> getTypeExpr(param, expr));
		if (param.containsKey(stmt.getVarDecl())) {
			Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>> replacement = param.get(stmt.getVarDecl());
			return List.of(Assign(replacement.get1(), cast(ArrayWriteExpr.of(cast(replacement.get1().getRef(), ArrayType.of(replacement.get1().getType().getIndexType(), replacement.get1().getType().getElemType())), replacement.get2(), cast(declTypeExpr.orElse(stmt.getExpr()), replacement.get1().getType().getElemType())), replacement.get1().getType())));
		}
		return List.of(declTypeExpr.map(declTypeExpr1 -> Assign(stmt.getVarDecl(), declTypeExpr1)).orElse(stmt));
	}

	@Override
	public <DeclType extends Type> List<Stmt> visit(HavocStmt<DeclType> stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		if (param.containsKey(stmt.getVarDecl())) {
			Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>> replacement = param.get(stmt.getVarDecl());
			return List.of(stmt, Assign(replacement.get1(), cast(ArrayWriteExpr.of(cast(replacement.get1().getRef(), ArrayType.of(replacement.get1().getType().getIndexType(), replacement.get1().getType().getElemType())), cast(replacement.get2(), replacement.get1().getType().getIndexType()), cast(stmt.getVarDecl().getRef(), replacement.get1().getType().getElemType())), replacement.get1().getType())));
		}
		return List.of(stmt);
	}

	@Override
	public List<Stmt> visit(XcfaStmt xcfaStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return xcfaStmt.accept(this, param);
	}

	@Override
	public List<Stmt> visit(SequenceStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<Stmt> visit(NonDetStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<Stmt> visit(OrtStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<Stmt> visit(LoopStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<Stmt> visit(XcfaCallStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		boolean needsTransformation = false;
		List<Expr<?>> exprs = new ArrayList<>();
		for (Expr<?> stmtParam : stmt.getParams()) {
			Optional<? extends Expr<?>> expr = ExpressionReplacer.replace(stmtParam, expr1 -> getTypeExpr(param, expr1));
			if(expr.isPresent()) {
				exprs.add(expr.get());
				needsTransformation = true;
			} else {
				exprs.add(stmtParam);
			}
		}
		if(needsTransformation) return List.of(new XcfaCallStmt(exprs, stmt.getProcedure()));
		return List.of(stmt);
	}

	@Override
	public List<Stmt> visit(StoreStmt storeStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		if (param.containsKey(storeStmt.getGlobal()) || param.containsKey(storeStmt.getLocal())) {
			throw new UnsupportedOperationException("Store/Load statements cannot be transformed to array write/reads!");
		}
		return List.of(storeStmt);
	}

	@Override
	public List<Stmt> visit(LoadStmt loadStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		if (param.containsKey(loadStmt.getGlobal()) || param.containsKey(loadStmt.getLocal())) {
			throw new UnsupportedOperationException("Store/Load statements cannot be transformed to array write/reads!");
		}
		return List.of(loadStmt);
	}

	@Override
	public List<Stmt> visit(FenceStmt fenceStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(fenceStmt);
	}

	@Override
	public List<Stmt> visit(AtomicBeginStmt atomicBeginStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(atomicBeginStmt);
	}

	@Override
	public List<Stmt> visit(AtomicEndStmt atomicEndStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(atomicEndStmt);
	}

	@Override
	public List<Stmt> visit(StartThreadStmt startThreadStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(startThreadStmt);
	}

	@Override
	public List<Stmt> visit(JoinThreadStmt joinThreadStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(joinThreadStmt);
	}
}
