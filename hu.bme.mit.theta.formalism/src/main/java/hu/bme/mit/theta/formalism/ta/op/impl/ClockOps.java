package hu.bme.mit.theta.formalism.ta.op.impl;

import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.expr.AddExpr;
import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.expr.IntLitExpr;
import hu.bme.mit.theta.core.stmt.AssignStmt;
import hu.bme.mit.theta.core.stmt.AssumeStmt;
import hu.bme.mit.theta.core.stmt.HavocStmt;
import hu.bme.mit.theta.core.stmt.Stmt;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.utils.impl.FailStmtVisitor;
import hu.bme.mit.theta.formalism.common.decl.ClockDecl;
import hu.bme.mit.theta.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.theta.formalism.ta.constr.ClockConstr;
import hu.bme.mit.theta.formalism.ta.constr.impl.ClockConstrs;
import hu.bme.mit.theta.formalism.ta.op.ClockOp;
import hu.bme.mit.theta.formalism.ta.op.CopyOp;
import hu.bme.mit.theta.formalism.ta.op.FreeOp;
import hu.bme.mit.theta.formalism.ta.op.GuardOp;
import hu.bme.mit.theta.formalism.ta.op.ResetOp;
import hu.bme.mit.theta.formalism.ta.op.ShiftOp;

public final class ClockOps {

	private static final StmtToClockOpVisitor VISITOR;

	static {
		VISITOR = new StmtToClockOpVisitor();
	}

	private ClockOps() {
	}

	////

	public static ClockOp fromStmt(final Stmt stmt) {
		return stmt.accept(VISITOR, null);
	}

	////

	public static CopyOp Copy(final ClockDecl clock, final ClockDecl value) {
		return new CopyOpImpl(clock, value);
	}

	public static FreeOp Free(final ClockDecl clock) {
		return new FreeOpImpl(clock);
	}

	public static GuardOp Guard(final ClockConstr constr) {
		return new GuardOpImpl(constr);
	}

	public static ResetOp Reset(final ClockDecl clock, final int value) {
		return new ResetOpImpl(clock, value);
	}

	public static ShiftOp Shift(final ClockDecl clock, final int offset) {
		return new ShifOpImpl(clock, offset);
	}

	////

	private static final class StmtToClockOpVisitor extends FailStmtVisitor<Void, ClockOp> {

		private StmtToClockOpVisitor() {
		}

		@Override
		public <LhsType extends Type> ClockOp visit(final HavocStmt<LhsType> stmt, final Void param) {
			final VarDecl<?> varDecl = stmt.getVarDecl();
			if (varDecl instanceof ClockDecl) {
				final ClockDecl clock = (ClockDecl) varDecl;
				return Free(clock);
			}

			throw new IllegalArgumentException();
		}

		@Override
		public <LhsType extends Type, RhsType extends LhsType> ClockOp visit(final AssignStmt<LhsType, RhsType> stmt,
				final Void param) {

			final VarDecl<?> varDecl = stmt.getVarDecl();

			if (varDecl instanceof ClockDecl) {
				final ClockDecl clock = (ClockDecl) varDecl;
				final Expr<?> expr = stmt.getExpr();

				if (expr instanceof IntLitExpr) {
					final IntLitExpr intLit = (IntLitExpr) expr;
					final int value = Math.toIntExact(intLit.getValue());
					return Reset(clock, value);

				} else if (expr instanceof ClockRefExpr) {
					final ClockRefExpr clockRef = (ClockRefExpr) expr;
					final ClockDecl value = clockRef.getDecl();
					return Copy(clock, value);

				} else if (expr instanceof AddExpr) {
					final ClockRefExpr clockRef = clock.getRef();
					final AddExpr<?> addExpr = (AddExpr<?>) expr;
					final Expr<?>[] ops = addExpr.getOps().toArray(new Expr<?>[0]);

					if (ops.length == 2) {
						if (ops[0].equals(clockRef)) {
							if (ops[1] instanceof IntLitExpr) {
								final IntLitExpr intLit = (IntLitExpr) ops[1];
								final int offset = Math.toIntExact(intLit.getValue());
								return Shift(clock, offset);
							}
						} else if (ops[1].equals(clockRef)) {
							if (ops[0] instanceof IntLitExpr) {
								final IntLitExpr intLit = (IntLitExpr) ops[0];
								final int offset = Math.toIntExact(intLit.getValue());
								return Shift(clock, offset);
							}
						}
					}
				}
			}

			throw new IllegalArgumentException();
		}

		@Override
		public ClockOp visit(final AssumeStmt stmt, final Void param) {
			try {
				final Expr<? extends BoolType> cond = stmt.getCond();
				final ClockConstr constr = ClockConstrs.formExpr(cond);
				return Guard(constr);

			} catch (final IllegalArgumentException e) {
				throw new IllegalArgumentException();
			}
		}

	}

}
