package hu.bme.mit.theta.core.utils;

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
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.booltype.AndExpr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.type.booltype.IffExpr;
import hu.bme.mit.theta.core.type.booltype.ImplyExpr;
import hu.bme.mit.theta.core.type.booltype.NotExpr;
import hu.bme.mit.theta.core.type.booltype.OrExpr;

public final class CnfTransformation {

	private static final String CNFPREFIX = "__CNF";
	private final CnfTransformationHelper helper;

	public CnfTransformation() {
		helper = new CnfTransformationHelper();
	}

	public Expr<BoolType> transform(final Expr<BoolType> expr) {
		final Collection<Expr<BoolType>> encoding = new ArrayList<>();
		final Expr<BoolType> top = helper.transform(expr, encoding);
		encoding.add(top);
		return And(encoding);
	}

	public Collection<VarDecl<BoolType>> getRepresentatives() {
		return helper.getReps();
	}

	private static final class CnfTransformationHelper {
		private int nextCnfVarId;
		private final Map<Expr<?>, VarDecl<BoolType>> representatives;

		private CnfTransformationHelper() {
			nextCnfVarId = 0;
			representatives = new HashMap<>();
		}

		public Collection<VarDecl<BoolType>> getReps() {
			return representatives.values();
		}

		public Expr<BoolType> transform(final Expr<BoolType> expr, final Collection<Expr<BoolType>> encoding) {
			if (expr instanceof NotExpr) {
				return encodeNot((NotExpr) expr, encoding);
			} else if (expr instanceof ImplyExpr) {
				return encodeImply((ImplyExpr) expr, encoding);
			} else if (expr instanceof IffExpr) {
				return encodeIff((IffExpr) expr, encoding);
			} else if (expr instanceof AndExpr) {
				return encodeAnd((AndExpr) expr, encoding);
			} else if (expr instanceof OrExpr) {
				return encodeOr((OrExpr) expr, encoding);
			} else {
				return expr;
			}
		}

		////

		private Expr<BoolType> getRep(final Expr<?> expr) {
			final VarDecl<BoolType> rep = Decls.Var(CNFPREFIX + (nextCnfVarId++), Bool());
			representatives.put(expr, rep);
			return rep.getRef();
		}

		////

		private Expr<BoolType> encodeNot(final NotExpr expr, final Collection<Expr<BoolType>> encoding) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Expr<BoolType> op = transform(expr.getOp(), encoding);
			encoding.add(And(Or(Not(rep), Not(op)), Or(rep, op)));
			return rep;
		}

		private Expr<BoolType> encodeImply(final ImplyExpr expr, final Collection<Expr<BoolType>> encoding) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Expr<BoolType> op1 = transform(expr.getLeftOp(), encoding);
			final Expr<BoolType> op2 = transform(expr.getRightOp(), encoding);
			encoding.add(And(Or(Not(rep), Not(op1), op2), Or(op1, rep), Or(Not(op2), rep)));
			return rep;
		}

		private Expr<BoolType> encodeIff(final IffExpr expr, final Collection<Expr<BoolType>> encoding) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Expr<BoolType> op1 = transform(expr.getLeftOp(), encoding);
			final Expr<BoolType> op2 = transform(expr.getRightOp(), encoding);
			encoding.add(And(Or(Not(rep), Not(op1), op2), Or(Not(rep), op1, Not(op2)), Or(rep, Not(op1), Not(op2)),
					Or(rep, op1, op2)));
			return rep;
		}

		private Expr<BoolType> encodeAnd(final AndExpr expr, final Collection<Expr<BoolType>> encoding) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Collection<Expr<BoolType>> ops = new ArrayList<>(expr.getOps().size());
			for (final Expr<BoolType> op : expr.getOps()) {
				ops.add(transform(op, encoding));
			}
			final Collection<Expr<BoolType>> lastClause = new ArrayList<>();
			lastClause.add(rep);
			final Collection<Expr<BoolType>> en = new ArrayList<>();
			for (final Expr<BoolType> op : ops) {
				en.add(Or(Not(rep), op));
				lastClause.add(Not(op));
			}
			en.add(Or(lastClause));
			encoding.add(And(en));
			return rep;
		}

		private Expr<BoolType> encodeOr(final OrExpr expr, final Collection<Expr<BoolType>> encoding) {
			if (representatives.containsKey(expr))
				return representatives.get(expr).getRef();
			final Expr<BoolType> rep = getRep(expr);
			final Collection<Expr<BoolType>> ops = new ArrayList<>(expr.getOps().size());
			for (final Expr<BoolType> op : expr.getOps()) {
				ops.add(transform(op, encoding));
			}
			final Collection<Expr<BoolType>> lastClause = new ArrayList<>();
			lastClause.add(Not(rep));
			final Collection<Expr<BoolType>> en = new ArrayList<>();
			for (final Expr<BoolType> op : ops) {
				en.add(Or(Not(op), rep));
				lastClause.add(op);
			}
			en.add(Or(lastClause));
			encoding.add(And(en));
			return rep;
		}

	}
}
