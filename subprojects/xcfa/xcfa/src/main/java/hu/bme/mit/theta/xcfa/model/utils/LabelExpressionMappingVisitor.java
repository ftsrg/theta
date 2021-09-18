package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.LoopStmt;
import hu.bme.mit.theta.core.stmt.NonDetStmt;
import hu.bme.mit.theta.core.stmt.OrtStmt;
import hu.bme.mit.theta.core.stmt.PopStmt;
import hu.bme.mit.theta.core.stmt.PushStmt;
import hu.bme.mit.theta.core.stmt.SequenceStmt;
import hu.bme.mit.theta.core.stmt.SkipStmt;
import hu.bme.mit.theta.core.stmt.Stmts;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabelVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.ProcedureCall;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.StartThread;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class LabelExpressionMappingVisitor<T extends Type> implements XcfaLabelVisitor<Function<Expr<T>, Optional<Expr<T>>>, Optional<XcfaLabel>> {
	@Override
	public Optional<XcfaLabel> visit(SkipStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel> visit(AssumeStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		Optional<Expr<BoolType>> exprOpt = ExpressionReplacer.replace(stmt.getCond(), param);
		return Optional.ofNullable((exprOpt.map(cond -> Stmt(Stmts.Assume(cond))).orElse(null)));
	}

	@Override
	public <DeclType extends Type> Optional<XcfaLabel> visit(AssignStmt<DeclType> stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		Optional<Expr<DeclType>> exprOpt = ExpressionReplacer.replace(stmt.getExpr(), param);
		return exprOpt.map(declTypeExpr -> Stmt(Assign(stmt.getVarDecl(), declTypeExpr)));
	}

	@Override
	public <DeclType extends Type> Optional<XcfaLabel> visit(HavocStmt<DeclType> stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel> visit(SequenceStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<XcfaLabel> visit(NonDetStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<XcfaLabel> visit(OrtStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<XcfaLabel> visit(LoopStmt stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public <DeclType extends Type> Optional<XcfaLabel> visit(PushStmt<DeclType> stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public <DeclType extends Type> Optional<XcfaLabel> visit(PopStmt<DeclType> stmt, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel> visit(XcfaLabel.ProcedureCallXcfaLabel label, Function<Expr<T>, Optional<Expr<T>>> param) {
		boolean needsTransformation = false;
		List<Expr<?>> exprs = new ArrayList<>();
		for (Expr<?> stmtParam : label.getParams()) {
			Optional<? extends Expr<?>> expr = ExpressionReplacer.replace(stmtParam, param);
			if(expr.isPresent()) {
				exprs.add(expr.get());
				needsTransformation = true;
			} else {
				exprs.add(stmtParam);
			}
		}
		if(needsTransformation) return Optional.of(ProcedureCall(exprs, label.getProcedure()));
		return Optional.empty();
	}

	@Override
	public <S extends Type> Optional<XcfaLabel> visit(XcfaLabel.StoreXcfaLabel<S> label, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public <S extends Type> Optional<XcfaLabel> visit(XcfaLabel.LoadXcfaLabel<S> label, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel> visit(XcfaLabel.FenceXcfaLabel label, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel> visit(XcfaLabel.AtomicBeginXcfaLabel label, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel> visit(XcfaLabel.AtomicEndXcfaLabel label, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel> visit(XcfaLabel.StartThreadXcfaLabel label, Function<Expr<T>, Optional<Expr<T>>> param) {
		Optional<? extends Expr<?>> exprOpt = ExpressionReplacer.replace(label.getParam(), param);
		return exprOpt.map(declTypeExpr -> StartThread(label.getKey(), label.getThreadName(), declTypeExpr));
	}

	@Override
	public Optional<XcfaLabel> visit(XcfaLabel.JoinThreadXcfaLabel label, Function<Expr<T>, Optional<Expr<T>>> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel> visit(XcfaLabel.StmtXcfaLabel label, Function<Expr<T>, Optional<Expr<T>>> param) {
		return label.getStmt().accept(this, param);
	}
}
