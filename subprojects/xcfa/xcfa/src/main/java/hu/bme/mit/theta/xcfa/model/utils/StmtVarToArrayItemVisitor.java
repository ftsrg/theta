package hu.bme.mit.theta.xcfa.model.utils;

import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.core.decl.Decl;
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
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.anytype.RefExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayType;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabelVisitor;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static hu.bme.mit.theta.core.stmt.Stmts.Assign;
import static hu.bme.mit.theta.core.utils.TypeUtils.cast;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.ProcedureCall;
import static hu.bme.mit.theta.xcfa.model.XcfaLabel.Stmt;

public class StmtVarToArrayItemVisitor<P extends Type> implements XcfaLabelVisitor<Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>>, List<XcfaLabel>> {

	private Optional<Expr<Type>> getTypeExpr(Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param, Expr<Type> expr) {
		if (expr instanceof RefExpr && param.containsKey(((RefExpr<Type>) expr).getDecl())) {
			Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>> replacement = param.get(((RefExpr<Type>) expr).getDecl());
			return Optional.of(cast(ArrayReadExpr.of(cast(replacement.get1().getRef(), replacement.get1().getType()), replacement.get2()), expr.getType()));
		}
		return Optional.empty();
	}


	@Override
	public List<XcfaLabel> visit(SkipStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(Stmt(stmt));
	}

	@Override
	public List<XcfaLabel> visit(AssumeStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		Optional<Expr<BoolType>> newExpr = ExpressionReplacer.replace(stmt.getCond(), expr -> getTypeExpr(param, (Expr<Type>) expr));
		return List.of(newExpr.map(cond -> Stmt(Stmts.Assume(cond))).orElse(Stmt(stmt)));
	}

	@Override
	public <DeclType extends Type> List<XcfaLabel> visit(AssignStmt<DeclType> stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		Optional<Expr<DeclType>> declTypeExpr = ExpressionReplacer.replace(stmt.getExpr(), expr -> getTypeExpr(param, (Expr<Type>) expr));
		if (param.containsKey(stmt.getVarDecl())) {
			Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>> replacement = param.get(stmt.getVarDecl());
			return List.of(Stmt(Assign(replacement.get1(), cast(ArrayWriteExpr.of(cast(replacement.get1().getRef(), ArrayType.of(replacement.get1().getType().getIndexType(), replacement.get1().getType().getElemType())), replacement.get2(), cast(declTypeExpr.orElse(stmt.getExpr()), replacement.get1().getType().getElemType())), replacement.get1().getType()))));
		}
		return List.of(Stmt(declTypeExpr.map(declTypeExpr1 -> Assign(stmt.getVarDecl(), declTypeExpr1)).orElse(stmt)));
	}

	@Override
	public <DeclType extends Type> List<XcfaLabel> visit(HavocStmt<DeclType> stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		if (param.containsKey(stmt.getVarDecl())) {
			Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>> replacement = param.get(stmt.getVarDecl());
			return List.of(Stmt(stmt), Stmt(Assign(replacement.get1(), cast(ArrayWriteExpr.of(cast(replacement.get1().getRef(), ArrayType.of(replacement.get1().getType().getIndexType(), replacement.get1().getType().getElemType())), cast(replacement.get2(), replacement.get1().getType().getIndexType()), cast(stmt.getVarDecl().getRef(), replacement.get1().getType().getElemType())), replacement.get1().getType()))));
		}
		return List.of(Stmt(stmt));
	}

	@Override
	public List<XcfaLabel> visit(SequenceStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<XcfaLabel> visit(NonDetStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<XcfaLabel> visit(OrtStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<XcfaLabel> visit(LoopStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public <DeclType extends Type> List<XcfaLabel> visit(PushStmt<DeclType> stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		if (param.containsKey(stmt.getVarDecl())) {
			Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>> replacement = param.get(stmt.getVarDecl());
			return List.of(Stmt(stmt), Stmt(Assign(replacement.get1(), cast(ArrayWriteExpr.of(cast(replacement.get1().getRef(), ArrayType.of(replacement.get1().getType().getIndexType(), replacement.get1().getType().getElemType())), cast(replacement.get2(), replacement.get1().getType().getIndexType()), cast(stmt.getVarDecl().getRef(), replacement.get1().getType().getElemType())), replacement.get1().getType()))));
		}
		return List.of(Stmt(stmt));	}

	@Override
	public <DeclType extends Type> List<XcfaLabel> visit(PopStmt<DeclType> stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		if (param.containsKey(stmt.getVarDecl())) {
			Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>> replacement = param.get(stmt.getVarDecl());
			return List.of(Stmt(stmt), Stmt(Assign(replacement.get1(), cast(ArrayWriteExpr.of(cast(replacement.get1().getRef(), ArrayType.of(replacement.get1().getType().getIndexType(), replacement.get1().getType().getElemType())), cast(replacement.get2(), replacement.get1().getType().getIndexType()), cast(stmt.getVarDecl().getRef(), replacement.get1().getType().getElemType())), replacement.get1().getType()))));
		}
		return List.of(Stmt(stmt));	}

	@Override
	public List<XcfaLabel> visit(IfStmt stmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<XcfaLabel> visit(XcfaLabel.ProcedureCallXcfaLabel label, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		boolean needsTransformation = false;
		List<Expr<?>> exprs = new ArrayList<>();
		for (Expr<?> stmtParam : label.getParams()) {
			Optional<? extends Expr<?>> expr = ExpressionReplacer.replace(stmtParam, expr1 -> getTypeExpr(param, (Expr<Type>) expr1));
			if(expr.isPresent()) {
				exprs.add(expr.get());
				needsTransformation = true;
			} else {
				exprs.add(stmtParam);
			}
		}
		if(needsTransformation) return List.of(ProcedureCall(exprs, label.getProcedure()));
		return List.of(label);
	}

	@Override
	public <S extends Type> List<XcfaLabel> visit(XcfaLabel.StoreXcfaLabel<S> label, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		if (param.containsKey(label.getGlobal()) || param.containsKey(label.getLocal())) {
			throw new UnsupportedOperationException("Store/Load statements cannot be transformed to array write/reads!");
		}
		return List.of(label);
	}

	@Override
	public <S extends Type> List<XcfaLabel> visit(XcfaLabel.LoadXcfaLabel<S> label, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		if (param.containsKey(label.getGlobal()) || param.containsKey(label.getLocal())) {
			throw new UnsupportedOperationException("Store/Load statements cannot be transformed to array write/reads!");
		}
		return List.of(label);
	}

	@Override
	public List<XcfaLabel> visit(XcfaLabel.FenceXcfaLabel fenceStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(fenceStmt);
	}

	@Override
	public List<XcfaLabel> visit(XcfaLabel.StmtXcfaLabel label, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return label.getStmt().accept(this, param);
	}

	@Override
	public List<XcfaLabel> visit(XcfaLabel.SequenceLabel sequenceLabel, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<XcfaLabel> visit(XcfaLabel.NondetLabel nondetLabel, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		throw new UnsupportedOperationException("Not yet implemented!");
	}

	@Override
	public List<XcfaLabel> visit(XcfaLabel.AtomicBeginXcfaLabel atomicBeginStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(atomicBeginStmt);
	}

	@Override
	public List<XcfaLabel> visit(XcfaLabel.AtomicEndXcfaLabel atomicEndStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(atomicEndStmt);
	}

	@Override
	public List<XcfaLabel> visit(XcfaLabel.StartThreadXcfaLabel startThreadStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(startThreadStmt);
	}

	@Override
	public List<XcfaLabel> visit(XcfaLabel.JoinThreadXcfaLabel joinThreadStmt, Map<Decl<?>, Tuple2<VarDecl<ArrayType<P, ?>>, LitExpr<P>>> param) {
		return List.of(joinThreadStmt);
	}
}
