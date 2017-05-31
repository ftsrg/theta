package hu.bme.mit.theta.core.utils.impl;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.And;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Bool;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Not;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.EqExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.GeqExpr;
import hu.bme.mit.theta.core.expr.GtExpr;
import hu.bme.mit.theta.core.expr.IteExpr;
import hu.bme.mit.theta.core.expr.LeqExpr;
import hu.bme.mit.theta.core.expr.LtExpr;
import hu.bme.mit.theta.core.expr.MulExpr;
import hu.bme.mit.theta.core.expr.NegExpr;
import hu.bme.mit.theta.core.expr.NeqExpr;
import hu.bme.mit.theta.core.expr.PrimedExpr;
import hu.bme.mit.theta.core.expr.RefExpr;
import hu.bme.mit.theta.core.expr.SubExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.arraytype.ArrayReadExpr;
import hu.bme.mit.theta.core.type.arraytype.ArrayWriteExpr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.ExistsExpr;
import hu.bme.mit.theta.core.type.booltype.FalseExpr;
import hu.bme.mit.theta.core.type.booltype.ForallExpr;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;
import hu.bme.mit.theta.core.type.booltype.TrueExpr;
import hu.bme.mit.theta.core.type.closure.ClosedUnderAdd;
import hu.bme.mit.theta.core.type.closure.ClosedUnderMul;
import hu.bme.mit.theta.core.type.closure.ClosedUnderNeg;
import hu.bme.mit.theta.core.type.closure.ClosedUnderSub;
import hu.bme.mit.theta.core.type.functype.FuncAppExpr;
import hu.bme.mit.theta.core.type.functype.FuncLitExpr;
import hu.bme.mit.theta.core.type.inttype.IntDivExpr;
import hu.bme.mit.theta.core.type.inttype.IntLitExpr;
import hu.bme.mit.theta.core.type.inttype.ModExpr;
import hu.bme.mit.theta.core.type.inttype.RemExpr;
import hu.bme.mit.theta.core.type.proctype.ProcCallExpr;
import hu.bme.mit.theta.core.type.rattype.RatDivExpr;
import hu.bme.mit.theta.core.type.rattype.RatLitExpr;
import hu.bme.mit.theta.core.utils.ExprVisitor;

public class CnfTransformation {
	private static final String CNFPREFIX = "__CNF";
	private final CNFTransformationVisitor cnfTransfVisitor;

	public CnfTransformation() {
		cnfTransfVisitor = new CNFTransformationVisitor();
	}

	public Expr<BoolType> transform(final Expr<BoolType> expr) {
		final Collection<Expr<BoolType>> encoding = new ArrayList<>();
		final Expr<BoolType> top = expr.accept(cnfTransfVisitor, encoding);
		encoding.add(top);
		return And(encoding);
	}

	public Collection<VarDecl<BoolType>> getRepresentatives() {
		return cnfTransfVisitor.getReps();
	}

	private static final class CNFTransformationVisitor
			implements ExprVisitor<Collection<Expr<BoolType>>, Expr<BoolType>> {

		private int nextCNFVarId;
		private final Map<Expr<?>, VarDecl<BoolType>> representatives;

		public CNFTransformationVisitor() {
			nextCNFVarId = 0;
			representatives = new HashMap<>();
		}

		public Collection<VarDecl<BoolType>> getReps() {
			return representatives.values();
		}

		private Expr<BoolType> getRep(final Expr<?> expr) {
			final VarDecl<BoolType> rep = Decls.Var(CNFPREFIX + (nextCNFVarId++), Bool());
			representatives.put(expr, rep);
			return rep.getRef();
		}

		@SuppressWarnings("unchecked")
		private Expr<BoolType> visitNonBoolConn(final Expr<?> expr) {
			return (Expr<BoolType>) expr;
		}

		@Override
		public <DeclType extends Type> Expr<BoolType> visit(final RefExpr<DeclType> expr,
				final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final FalseExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final TrueExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final NotExpr expr, final Collection<Expr<BoolType>> param) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Expr<BoolType> op = expr.getOp().accept(this, param);
			param.add(And(Or(Not(rep), Not(op)), Or(rep, op)));
			return rep;
		}

		@Override
		public Expr<BoolType> visit(final ImplyExpr expr, final Collection<Expr<BoolType>> param) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Expr<BoolType> op1 = expr.getLeftOp().accept(this, param);
			final Expr<BoolType> op2 = expr.getRightOp().accept(this, param);
			param.add(And(Or(Not(rep), Not(op1), op2), Or(op1, rep), Or(Not(op2), rep)));
			return rep;
		}

		@Override
		public Expr<BoolType> visit(final IffExpr expr, final Collection<Expr<BoolType>> param) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Expr<BoolType> op1 = expr.getLeftOp().accept(this, param);
			final Expr<BoolType> op2 = expr.getRightOp().accept(this, param);
			param.add(And(Or(Not(rep), Not(op1), op2), Or(Not(rep), op1, Not(op2)), Or(rep, Not(op1), Not(op2)),
					Or(rep, op1, op2)));
			return rep;
		}

		@Override
		public Expr<BoolType> visit(final AndExpr expr, final Collection<Expr<BoolType>> param) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Collection<Expr<BoolType>> ops = new ArrayList<>(expr.getOps().size());
			for (final Expr<BoolType> op : expr.getOps())
				ops.add(op.accept(this, param));
			final Collection<Expr<BoolType>> lastClause = new ArrayList<>();
			lastClause.add(rep);
			final Collection<Expr<BoolType>> en = new ArrayList<>();
			for (final Expr<BoolType> op : ops) {
				en.add(Or(Not(rep), op));
				lastClause.add(Not(op));
			}
			en.add(Or(lastClause));
			param.add(And(en));
			return rep;
		}

		@Override
		public Expr<BoolType> visit(final OrExpr expr, final Collection<Expr<BoolType>> param) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Collection<Expr<BoolType>> ops = new ArrayList<>(expr.getOps().size());
			for (final Expr<BoolType> op : expr.getOps())
				ops.add(op.accept(this, param));
			final Collection<Expr<BoolType>> lastClause = new ArrayList<>();
			lastClause.add(Not(rep));
			final Collection<Expr<BoolType>> en = new ArrayList<>();
			for (final Expr<BoolType> op : ops) {
				en.add(Or(Not(op), rep));
				lastClause.add(op);
			}
			en.add(Or(lastClause));
			param.add(And(en));
			return rep;
		}

		@Override
		public Expr<BoolType> visit(final ExistsExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final ForallExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final EqExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final NeqExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final GeqExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final GtExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final LeqExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final LtExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final IntLitExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final IntDivExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final RemExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final ModExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final RatLitExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public Expr<BoolType> visit(final RatDivExpr expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends ClosedUnderNeg> Expr<BoolType> visit(final NegExpr<ExprType> expr,
				final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends ClosedUnderSub> Expr<BoolType> visit(final SubExpr<ExprType> expr,
				final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends ClosedUnderAdd> Expr<BoolType> visit(final AddExpr<ExprType> expr,
				final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends ClosedUnderMul> Expr<BoolType> visit(final MulExpr<ExprType> expr,
				final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> Expr<BoolType> visit(
				final ArrayReadExpr<IndexType, ElemType> expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <IndexType extends Type, ElemType extends Type> Expr<BoolType> visit(
				final ArrayWriteExpr<IndexType, ElemType> expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> Expr<BoolType> visit(
				final FuncLitExpr<ParamType, ResultType> expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ParamType extends Type, ResultType extends Type> Expr<BoolType> visit(
				final FuncAppExpr<ParamType, ResultType> expr, final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends Type> Expr<BoolType> visit(final IteExpr<ExprType> expr,
				final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ExprType extends Type> Expr<BoolType> visit(final PrimedExpr<ExprType> expr,
				final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

		@Override
		public <ReturnType extends Type> Expr<BoolType> visit(final ProcCallExpr<ReturnType> expr,
				final Collection<Expr<BoolType>> param) {
			return visitNonBoolConn(expr);
		}

	}
}
