package hu.bme.mit.inf.ttmc.formalism.utils.impl;

import static hu.bme.mit.inf.ttmc.formalism.common.expr.impl.Exprs2.Ref;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import com.google.common.collect.ImmutableSet;

import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayReadExpr;
import hu.bme.mit.inf.ttmc.core.expr.ArrayWriteExpr;
import hu.bme.mit.inf.ttmc.core.expr.ConstRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.ExistsExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.FalseExpr;
import hu.bme.mit.inf.ttmc.core.expr.ForallExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncAppExpr;
import hu.bme.mit.inf.ttmc.core.expr.FuncLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.core.expr.IffExpr;
import hu.bme.mit.inf.ttmc.core.expr.ImplyExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.IteExpr;
import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.core.expr.ModExpr;
import hu.bme.mit.inf.ttmc.core.expr.MulExpr;
import hu.bme.mit.inf.ttmc.core.expr.NegExpr;
import hu.bme.mit.inf.ttmc.core.expr.NeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.NotExpr;
import hu.bme.mit.inf.ttmc.core.expr.OrExpr;
import hu.bme.mit.inf.ttmc.core.expr.ParamRefExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatDivExpr;
import hu.bme.mit.inf.ttmc.core.expr.RatLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.RemExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.expr.impl.Exprs;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderMul;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.inf.ttmc.core.type.closure.ClosedUnderSub;
import hu.bme.mit.inf.ttmc.core.type.impl.Types;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2;
import hu.bme.mit.inf.ttmc.formalism.common.expr.PrimedExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcCallExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ProcRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.expr.VarRefExpr;
import hu.bme.mit.inf.ttmc.formalism.utils.FormalismExprVisitor;

public class CNFTransformation {
	private final String CNFPREFIX = "__CNF";
	private final CNFTransformationVisitor cnfTransfVisitor;

	public CNFTransformation() {
		cnfTransfVisitor = new CNFTransformationVisitor();
	}

	public Expr<? extends BoolType> transform(final Expr<? extends BoolType> expr) {
		final Collection<Expr<? extends BoolType>> encoding = new ArrayList<>();
		final Expr<? extends BoolType> top = expr.accept(cnfTransfVisitor, encoding);
		encoding.add(top);
		return Exprs.And(encoding);
	}

	public Collection<VarDecl<? extends BoolType>> getRepresentatives() {
		return cnfTransfVisitor.getReps();
	}

	public void clearRepresentatives() {
		cnfTransfVisitor.clearReps();
	}

	private final class CNFTransformationVisitor
			implements FormalismExprVisitor<Collection<Expr<? extends BoolType>>, Expr<? extends BoolType>> {

		private int nextCNFVarId;
		private final Map<Expr<?>, VarDecl<? extends BoolType>> representatives;

		public CNFTransformationVisitor() {
			nextCNFVarId = 0;
			representatives = new HashMap<>();
		}

		public Collection<VarDecl<? extends BoolType>> getReps() {
			return representatives.values();
		}

		public void clearReps() {
			representatives.clear();
		}

		private Expr<? extends BoolType> getRep(final Expr<?> expr) {
			final VarDecl<BoolType> rep = Decls2.Var(CNFPREFIX + (nextCNFVarId++), Types.Bool());
			representatives.put(expr, rep);
			return Ref(rep);
		}

		@SuppressWarnings("unchecked")
		private Expr<? extends BoolType> visitNonBoolConn(final Expr<? extends Type> expr) {
			return (Expr<? extends BoolType>) expr;
		}

		@Override
		public <DeclType extends Type> Expr<? extends BoolType> visit(final ConstRefExpr<DeclType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <DeclType extends Type> Expr<? extends BoolType> visit(final ParamRefExpr<DeclType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final FalseExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final TrueExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final NotExpr expr, final Collection<Expr<? extends BoolType>> param) {
			if (representatives.containsKey(expr))
				return Ref(representatives.get(expr));
			final Expr<? extends BoolType> rep = getRep(expr);
			final Expr<? extends BoolType> op = expr.getOp().accept(this, param);
			param.add(Exprs.And(ImmutableSet.of(Exprs.Or(ImmutableSet.of(Exprs.Not(rep), Exprs.Not(op))),
					Exprs.Or(ImmutableSet.of(rep, op)))));
			return rep;
		}

		@Override
		public Expr<? extends BoolType> visit(final ImplyExpr expr, final Collection<Expr<? extends BoolType>> param) {
			if (representatives.containsKey(expr))
				return Ref(representatives.get(expr));
			final Expr<? extends BoolType> rep = getRep(expr);
			final Expr<? extends BoolType> op1 = expr.getLeftOp().accept(this, param);
			final Expr<? extends BoolType> op2 = expr.getRightOp().accept(this, param);
			param.add(Exprs.And(ImmutableSet.of(Exprs.Or(ImmutableSet.of(Exprs.Not(rep), Exprs.Not(op1), op2)),
					Exprs.Or(ImmutableSet.of(op1, rep)), Exprs.Or(ImmutableSet.of(Exprs.Not(op2), rep)))));
			return rep;
		}

		@Override
		public Expr<? extends BoolType> visit(final IffExpr expr, final Collection<Expr<? extends BoolType>> param) {
			if (representatives.containsKey(expr))
				return Ref(representatives.get(expr));
			final Expr<? extends BoolType> rep = getRep(expr);
			final Expr<? extends BoolType> op1 = expr.getLeftOp().accept(this, param);
			final Expr<? extends BoolType> op2 = expr.getRightOp().accept(this, param);
			param.add(Exprs.And(ImmutableSet.of(Exprs.Or(ImmutableSet.of(Exprs.Not(rep), Exprs.Not(op1), op2)),
					Exprs.Or(ImmutableSet.of(Exprs.Not(rep), op1, Exprs.Not(op2))),
					Exprs.Or(ImmutableSet.of(rep, Exprs.Not(op1), Exprs.Not(op2))),
					Exprs.Or(ImmutableSet.of(rep, op1, op2)))));
			return rep;
		}

		@Override
		public Expr<? extends BoolType> visit(final AndExpr expr, final Collection<Expr<? extends BoolType>> param) {
			if (representatives.containsKey(expr))
				return Ref(representatives.get(expr));
			final Expr<? extends BoolType> rep = getRep(expr);
			final Collection<Expr<? extends BoolType>> ops = new ArrayList<>(expr.getOps().size());
			for (final Expr<? extends BoolType> op : expr.getOps())
				ops.add(op.accept(this, param));
			final Collection<Expr<? extends BoolType>> lastClause = new ArrayList<>();
			lastClause.add(rep);
			final Collection<Expr<? extends BoolType>> en = new ArrayList<>();
			for (final Expr<? extends BoolType> op : ops) {
				en.add(Exprs.Or(ImmutableSet.of(Exprs.Not(rep), op)));
				lastClause.add(Exprs.Not(op));
			}
			en.add(Exprs.Or(lastClause));
			param.add(Exprs.And(en));
			return rep;
		}

		@Override
		public Expr<? extends BoolType> visit(final OrExpr expr, final Collection<Expr<? extends BoolType>> param) {
			if (representatives.containsKey(expr))
				return Ref(representatives.get(expr));
			final Expr<? extends BoolType> rep = getRep(expr);
			final Collection<Expr<? extends BoolType>> ops = new ArrayList<>(expr.getOps().size());
			for (final Expr<? extends BoolType> op : expr.getOps())
				ops.add(op.accept(this, param));
			final Collection<Expr<? extends BoolType>> lastClause = new ArrayList<>();
			lastClause.add(Exprs.Not(rep));
			final Collection<Expr<? extends BoolType>> en = new ArrayList<>();
			for (final Expr<? extends BoolType> op : ops) {
				en.add(Exprs.Or(ImmutableSet.of(Exprs.Not(op), rep)));
				lastClause.add(op);
			}
			en.add(Exprs.Or(lastClause));
			param.add(Exprs.And(en));
			return rep;
		}

		@Override
		public Expr<? extends BoolType> visit(final ExistsExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final ForallExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final EqExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final NeqExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final GeqExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final GtExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final LeqExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final LtExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final IntLitExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final IntDivExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final RemExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final ModExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final RatLitExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<? extends BoolType> visit(final RatDivExpr expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends ClosedUnderNeg> Expr<? extends BoolType> visit(final NegExpr<ExprType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends ClosedUnderSub> Expr<? extends BoolType> visit(final SubExpr<ExprType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends ClosedUnderAdd> Expr<? extends BoolType> visit(final AddExpr<ExprType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends ClosedUnderMul> Expr<? extends BoolType> visit(final MulExpr<ExprType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> Expr<? extends BoolType> visit(
				final ArrayReadExpr<IndexType, ElemType> expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> Expr<? extends BoolType> visit(
				final ArrayWriteExpr<IndexType, ElemType> expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> Expr<? extends BoolType> visit(
				final FuncLitExpr<ParamType, ResultType> expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> Expr<? extends BoolType> visit(
				final FuncAppExpr<ParamType, ResultType> expr, final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends Type> Expr<? extends BoolType> visit(final IteExpr<ExprType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends Type> Expr<? extends BoolType> visit(final PrimedExpr<ExprType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <DeclType extends Type> Expr<? extends BoolType> visit(final VarRefExpr<DeclType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ReturnType extends Type> Expr<? extends BoolType> visit(final ProcCallExpr<ReturnType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ReturnType extends Type> Expr<? extends BoolType> visit(final ProcRefExpr<ReturnType> expr,
				final Collection<Expr<? extends BoolType>> param) {
			return visitNonBoolConn(expr);
		}
	}
}
