package hu.bme.mit.theta.xcfa.model.utils;

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
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.core.utils.StmtAtomCollector;
import hu.bme.mit.theta.xcfa.model.XcfaLabel;
import hu.bme.mit.theta.xcfa.model.XcfaLabelVisitor;

import java.util.Collection;

import static hu.bme.mit.theta.core.type.abstracttype.AbstractExprs.Eq;

public class XcfaAtomCollecter implements XcfaLabelVisitor<Collection<Expr<BoolType>>, Void> {
	public static XcfaAtomCollecter INSTANCE = new XcfaAtomCollecter();

	@Override
	public Void visit(SkipStmt stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));
		return null;
	}

	@Override
	public Void visit(AssumeStmt stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(AssignStmt<DeclType> stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(HavocStmt<DeclType> stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public Void visit(SequenceStmt stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public Void visit(NonDetStmt stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public Void visit(OrtStmt stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public Void visit(LoopStmt stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(PushStmt<DeclType> stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public <DeclType extends Type> Void visit(PopStmt<DeclType> stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public Void visit(IfStmt stmt, Collection<Expr<BoolType>> param) {
		param.addAll(StmtAtomCollector.collectAtoms(stmt));

		return null;
	}

	@Override
	public Void visit(XcfaLabel.AtomicBeginXcfaLabel label, Collection<Expr<BoolType>> param) {
		return null;
	}

	@Override
	public Void visit(XcfaLabel.AtomicEndXcfaLabel label, Collection<Expr<BoolType>> param) {
		return null;
	}

	@Override
	public Void visit(XcfaLabel.ProcedureCallXcfaLabel label, Collection<Expr<BoolType>> param) {
		throw new UnsupportedOperationException("Cannot get atoms of ProcedureCalls - did you mean to inline before?");
	}

	@Override
	public Void visit(XcfaLabel.StartThreadXcfaLabel label, Collection<Expr<BoolType>> param) {
		return null;
	}

	@Override
	public Void visit(XcfaLabel.JoinThreadXcfaLabel label, Collection<Expr<BoolType>> param) {
		return null;
	}

	@Override
	public <T extends Type> Void visit(XcfaLabel.LoadXcfaLabel<T> label, Collection<Expr<BoolType>> param) {
		ExprUtils.collectAtoms(Eq(label.getGlobal().getRef(), label.getLocal().getRef()), param);
		return null;
	}

	@Override
	public <T extends Type> Void visit(XcfaLabel.StoreXcfaLabel<T> label, Collection<Expr<BoolType>> param) {
		ExprUtils.collectAtoms(Eq(label.getGlobal().getRef(), label.getLocal().getRef()), param);
		return null;
	}

	@Override
	public Void visit(XcfaLabel.FenceXcfaLabel label, Collection<Expr<BoolType>> param) {
		return null;
	}

	@Override
	public Void visit(XcfaLabel.StmtXcfaLabel label, Collection<Expr<BoolType>> param) {
		return label.getStmt().accept(this, param);
	}

	@Override
	public Void visit(XcfaLabel.SequenceLabel sequenceLabel, Collection<Expr<BoolType>> param) {
		for (XcfaLabel label : sequenceLabel.getLabels()) {
			label.accept(this, param);
		}
		return null;
	}

	@Override
	public Void visit(XcfaLabel.NondetLabel nondetLabel, Collection<Expr<BoolType>> param) {
		for (XcfaLabel label : nondetLabel.getLabels()) {
			label.accept(this, param);
		}
		return null;
	}
}
