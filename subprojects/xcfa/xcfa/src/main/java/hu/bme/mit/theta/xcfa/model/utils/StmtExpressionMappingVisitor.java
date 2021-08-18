package hu.bme.mit.theta.xcfa.model.utils;

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
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;

public class StmtExpressionMappingVisitor<T extends Type> implements XcfaStmtVisitor<Function<Expr<T>, Optional<Expr<T>>>, Optional<Stmt>> {
	@Override
	public Optional<Stmt> visit(SkipStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<Stmt> visit(AssumeStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		Optional<Expr<BoolType>> exprOpt = ExpressionReplacer.replace(stmt.getCond(), param);
		return Optional.ofNullable(exprOpt.map(Stmts::Assume).orElse(null));
	}

	@Override
	public <DeclType extends Type> Optional<Stmt> visit(AssignStmt<DeclType> stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		Optional<Expr<DeclType>> exprOpt = ExpressionReplacer.replace(stmt.getExpr(), param);
		return exprOpt.map(declTypeExpr -> Assign(stmt.getVarDecl(), declTypeExpr));
	}

	@Override
	public <DeclType extends Type> Optional<Stmt> visit(HavocStmt<DeclType> stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<Stmt> visit(XcfaStmt xcfaStmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return xcfaStmt.accept(this, param);
	}

	@Override
	public Optional<Stmt> visit(SequenceStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<Stmt> visit(NonDetStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<Stmt> visit(OrtStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<Stmt> visit(LoopStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<Stmt> visit(XcfaCallStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		boolean needsTransformation = false;
		List<Expr<?>> exprs = new ArrayList<>();
		for (Expr<?> stmtParam : stmt.getParams()) {
			Optional<? extends Expr<?>> expr = ExpressionReplacer.replace(stmtParam, param);
			if(expr.isPresent()) {
				exprs.add(expr.get());
				needsTransformation = true;
			} else {
				exprs.add(stmtParam);
			}
		}
		if(needsTransformation) return Optional.of(new XcfaCallStmt(exprs, stmt.getProcedure()));
		return Optional.empty();
	}

	@Override
	public Optional<Stmt> visit(StoreStmt storeStmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<Stmt> visit(LoadStmt loadStmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<Stmt> visit(FenceStmt fenceStmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<Stmt> visit(AtomicBeginStmt atomicBeginStmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<Stmt> visit(AtomicEndStmt atomicEndStmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<Stmt> visit(StartThreadStmt startThreadStmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		Optional<? extends Expr<?>> exprOpt = ExpressionReplacer.replace(startThreadStmt.getParam(), param);
		return exprOpt.map(declTypeExpr -> new StartThreadStmt(startThreadStmt.getKey(), startThreadStmt.getThreadName(), declTypeExpr));
	}

	@Override
	public Optional<Stmt> visit(JoinThreadStmt joinThreadStmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}
}
