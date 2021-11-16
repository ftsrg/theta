package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.IfStmt;
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
import hu.bme.mit.theta.frontend.FrontendMetadata;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabelVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Function;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.stmt.Stmts.Havoc;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.ProcedureCall;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.StartThread;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class LabelExpressionMappingVisitor<T extends Type> implements XcfaLabelVisitor<LabelExpressionMappingVisitor.Mapper<T>, Optional<XcfaLabel>> {
	@Override
	public Optional<XcfaLabel>visit(SkipStmt stmt, Mapper<T> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel>visit(AssumeStmt stmt, Mapper<T> param) {
		Optional<Expr<BoolType>> exprOpt = ExpressionReplacer.replace(stmt.getCond(), param.getExprMapper());
		return Optional.ofNullable((exprOpt.map(cond -> Stmt(Stmts.Assume(cond))).orElse(null)));
	}

	@Override
	public <DeclType extends Type> Optional<XcfaLabel>visit(AssignStmt<DeclType> stmt, Mapper<T> param) {
		final Optional<VarDecl<T>> var = param.getVarMapper().apply(stmt.getVarDecl());
		Optional<Expr<DeclType>> exprOpt = ExpressionReplacer.replace(stmt.getExpr(), param.getExprMapper());
		return var.map(tVarDecl -> (XcfaLabel) Stmt(Assign(tVarDecl, cast(exprOpt.orElse(stmt.getExpr()), tVarDecl.getType())))).or(() -> exprOpt.map(declTypeExpr -> Stmt(Assign(stmt.getVarDecl(), declTypeExpr))));
	}

	@Override
	public <DeclType extends Type> Optional<XcfaLabel>visit(HavocStmt<DeclType> stmt, Mapper<T> param) {
		return param.getVarMapper().apply(stmt.getVarDecl()).map(tVarDecl -> {
			final HavocStmt<T> havoc = Havoc(tVarDecl);
			FrontendMetadata.lookupMetadata(stmt).forEach((s, o) -> FrontendMetadata.create(havoc, s, o));
			return Stmt(havoc);
		});
	}

	@Override
	public Optional<XcfaLabel>visit(SequenceStmt stmt, Mapper<T> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<XcfaLabel>visit(NonDetStmt stmt, Mapper<T> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<XcfaLabel>visit(OrtStmt stmt, Mapper<T> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public Optional<XcfaLabel>visit(LoopStmt stmt, Mapper<T> param) {
		throw new UnsupportedOperationException("Not yet implemented");
	}

	@Override
	public <DeclType extends Type> Optional<XcfaLabel>visit(PushStmt<DeclType> stmt, Mapper<T> param) {
		return Optional.empty();
	}

	@Override
	public <DeclType extends Type> Optional<XcfaLabel>visit(PopStmt<DeclType> stmt, Mapper<T> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel>visit(IfStmt stmt, Mapper<T> param) {
		Optional<Expr<BoolType>> condOpt = ExpressionReplacer.replace(stmt.getCond(), param.getExprMapper());
		Optional<XcfaLabel>thenOpt = stmt.getThen().accept(this, param);
		Optional<XcfaLabel>elzeOpt = stmt.getElze().accept(this, param);
		if (condOpt.isPresent() || thenOpt.isPresent() || elzeOpt.isPresent()) {
			return Optional.of(Stmt(IfStmt.of(condOpt.orElse(stmt.getCond()), thenOpt.map(XcfaLabel::getStmt).orElse(stmt.getThen()), elzeOpt.map(XcfaLabel::getStmt).orElse(stmt.getElze()))));
		}
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel>visit(XcfaLabel.ProcedureCallXcfaLabel label, Mapper<T> param) {
		boolean needsTransformation = false;
		List<Expr<?>> exprs = new ArrayList<>();
		for (Expr<?> stmtParam : label.getParams()) {
			Optional<? extends Expr<?>> expr = ExpressionReplacer.replace(stmtParam, param.getExprMapper());
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
	public <S extends Type> Optional<XcfaLabel>visit(XcfaLabel.StoreXcfaLabel<S> label, Mapper<T> param) {
		return Optional.empty();
	}

	@Override
	public <S extends Type> Optional<XcfaLabel>visit(XcfaLabel.LoadXcfaLabel<S> label, Mapper<T> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel>visit(XcfaLabel.FenceXcfaLabel label, Mapper<T> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel>visit(XcfaLabel.AtomicBeginXcfaLabel label, Mapper<T> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel>visit(XcfaLabel.AtomicEndXcfaLabel label, Mapper<T> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel>visit(XcfaLabel.StartThreadXcfaLabel label, Mapper<T> param) {
		Optional<? extends Expr<?>> exprOpt = ExpressionReplacer.replace(label.getParam(), param.getExprMapper());
		return exprOpt.map(declTypeExpr -> StartThread(label.getKey(), label.getThreadName(), declTypeExpr));
	}

	@Override
	public Optional<XcfaLabel>visit(XcfaLabel.JoinThreadXcfaLabel label, Mapper<T> param) {
		return Optional.empty();
	}

	@Override
	public Optional<XcfaLabel>visit(XcfaLabel.StmtXcfaLabel label, Mapper<T> param) {
		return label.getStmt().accept(this, param);
	}

	@Override
	public Optional<XcfaLabel> visit(XcfaLabel.SequenceLabel sequenceLabel, Mapper<T> param) {
		final List<XcfaLabel> collect = sequenceLabel.getLabels().stream().map(label -> label.accept(this, param).orElse(label)).collect(Collectors.toList());
		if(sequenceLabel.getLabels().equals(collect)) return Optional.empty();
		else return Optional.of(XcfaLabel.SequenceLabel.of(collect));
	}

	@Override
	public Optional<XcfaLabel> visit(XcfaLabel.NondetLabel nondetLabel, Mapper<T> param) {
		final List<XcfaLabel> collect = nondetLabel.getLabels().stream().map(label -> label.accept(this, param).orElse(label)).collect(Collectors.toList());
		if(nondetLabel.getLabels().equals(collect)) return Optional.empty();
		else return Optional.of(XcfaLabel.NondetLabel.of(collect));
	}


	public static class Mapper<T extends Type> {
		private final Function<Expr<?>, Optional<Expr<T>>> exprMapper;
		private final Function<VarDecl<?>, Optional<VarDecl<T>>> varMapper;

		private Mapper(final Function<Expr<?>, Optional<Expr<T>>> exprMapper, final Function<VarDecl<?>, Optional<VarDecl<T>>> varMapper) {
			this.exprMapper = exprMapper;
			this.varMapper = varMapper;
		}

		public static <T extends Type> Mapper<T> create(final Function<Expr<?>, Optional<Expr<T>>> exprMapper, final Function<VarDecl<?>, Optional<VarDecl<T>>> varMapper) {
			return new Mapper<T>(exprMapper, varMapper);
		}

		public Function<Expr<?>, Optional<Expr<T>>> getExprMapper() {
			return exprMapper;
		}

		public Function<VarDecl<?>, Optional<VarDecl<T>>> getVarMapper() {
			return varMapper;
		}
	}
}
