package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static hu.bme.mit.inf.ttmc.formalism.utils.FormalismUtils.collectVars;

import hu.bme.mit.inf.ttmc.core.expr.AddExpr;
import hu.bme.mit.inf.ttmc.core.expr.AndExpr;
import hu.bme.mit.inf.ttmc.core.expr.BinaryExpr;
import hu.bme.mit.inf.ttmc.core.expr.EqExpr;
import hu.bme.mit.inf.ttmc.core.expr.Expr;
import hu.bme.mit.inf.ttmc.core.expr.GeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.GtExpr;
import hu.bme.mit.inf.ttmc.core.expr.IntLitExpr;
import hu.bme.mit.inf.ttmc.core.expr.LeqExpr;
import hu.bme.mit.inf.ttmc.core.expr.LtExpr;
import hu.bme.mit.inf.ttmc.core.expr.SubExpr;
import hu.bme.mit.inf.ttmc.core.expr.TrueExpr;
import hu.bme.mit.inf.ttmc.core.type.BoolType;
import hu.bme.mit.inf.ttmc.core.type.Type;
import hu.bme.mit.inf.ttmc.core.utils.impl.FailExprVisitor;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.common.decl.VarDecl;
import hu.bme.mit.inf.ttmc.formalism.common.expr.ClockRefExpr;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssignStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.AssumeStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.HavocStmt;
import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.utils.FailStmtVisitor;

public final class TCFAUtils {

	private static final ClockStmtVisitor CLOCK_STMT_VISITOR;
	private static final ClockExprVisitor CLOCK_EXPR_VISITOR;
	private static final DataStmtVisitor DATA_STMT_VISITOR;

	static {
		CLOCK_STMT_VISITOR = new ClockStmtVisitor();
		CLOCK_EXPR_VISITOR = new ClockExprVisitor();
		DATA_STMT_VISITOR = new DataStmtVisitor();
	}

	private TCFAUtils() {
	}

	public static boolean isClockStmt(final Stmt stmt) {
		return stmt.accept(CLOCK_STMT_VISITOR, null);
	}

	public static boolean isClockExpr(final Expr<? extends BoolType> expr) {
		return expr.accept(CLOCK_EXPR_VISITOR, null);
	}

	public static boolean isDataStmt(final Stmt stmt) {
		return stmt.accept(DATA_STMT_VISITOR, null);
	}

	public static boolean isDataExpr(final Expr<? extends BoolType> expr) {
		return collectVars(expr).stream().allMatch(v -> !isClock(v));
	}

	private static boolean isClock(final VarDecl<?> varDecl) {
		return varDecl instanceof ClockDecl;
	}

	private static final class ClockStmtVisitor extends FailStmtVisitor<Void, Boolean> {

		private ClockStmtVisitor() {
		}

		@Override
		public <LhsType extends Type> Boolean visit(final HavocStmt<LhsType> stmt, final Void param) {
			return isClock(stmt.getVarDecl());
		}

		@Override
		public <LhsType extends Type, RhsType extends LhsType> Boolean visit(final AssignStmt<LhsType, RhsType> stmt,
				final Void param) {

			final VarDecl<?> varDecl = stmt.getVarDecl();
			if (varDecl instanceof ClockDecl) {
				final ClockDecl clock = (ClockDecl) varDecl;
				final Expr<?> rhs = stmt.getExpr();

				return isResetRhs(rhs) || isCopyRhs(rhs) || isShiftRhs(clock, rhs);
			}

			return false;

		}

		private boolean isResetRhs(final Expr<?> rhs) {
			return rhs instanceof IntLitExpr;
		}

		private boolean isCopyRhs(final Expr<?> rhs) {
			return rhs instanceof ClockRefExpr;
		}

		private boolean isShiftRhs(final ClockDecl clock, final Expr<?> rhs) {
			final ClockRefExpr clockRef = clock.getRef();

			if (rhs instanceof AddExpr<?>) {
				final AddExpr<?> addExpr = (AddExpr<?>) rhs;
				final Expr<?>[] ops = addExpr.getOps().toArray(new Expr<?>[0]);

				if (ops.length == 2) {
					if (ops[0].equals(clockRef)) {
						return ops[1] instanceof IntLitExpr;

					} else if (ops[1].equals(clockRef)) {
						return ops[0] instanceof IntLitExpr;
					}
				}
			}

			return false;
		}

		@Override
		public Boolean visit(final AssumeStmt stmt, final Void param) {
			return isClockExpr(stmt.getCond());
		}

	}

	private static final class ClockExprVisitor extends FailExprVisitor<Void, Boolean> {

		private ClockExprVisitor() {
		}

		@Override
		public Boolean visit(final TrueExpr expr, final Void param) {
			return true;
		}

		@Override
		public Boolean visit(final LtExpr expr, final Void param) {
			return hasClockConstrStructure(expr);
		}

		@Override
		public Boolean visit(final LeqExpr expr, final Void param) {
			return hasClockConstrStructure(expr);
		}

		@Override
		public Boolean visit(final GtExpr expr, final Void param) {
			return hasClockConstrStructure(expr);
		}

		@Override
		public Boolean visit(final GeqExpr expr, final Void param) {
			return hasClockConstrStructure(expr);
		}

		@Override
		public Boolean visit(final EqExpr expr, final Void param) {
			return hasClockConstrStructure(expr);
		}

		@Override
		public Boolean visit(final AndExpr expr, final Void param) {
			return expr.getOps().stream().allMatch(op -> op.accept(this, null));
		}

		private static boolean hasClockConstrStructure(final BinaryExpr<?, ?, ?> expr) {
			if (expr.getRightOp() instanceof IntLitExpr) {
				final Expr<?> leftOp = expr.getLeftOp();

				if (leftOp instanceof ClockRefExpr) {
					return true;
				} else if (leftOp instanceof SubExpr) {
					final SubExpr<?> subExpr = (SubExpr<?>) leftOp;
					return subExpr.getRightOp() instanceof ClockRefExpr && subExpr.getRightOp() instanceof ClockRefExpr;
				}
			}

			return false;
		}

	}

	private static final class DataStmtVisitor extends FailStmtVisitor<Void, Boolean> {

		private DataStmtVisitor() {
		}

		@Override
		public <LhsType extends Type> Boolean visit(final HavocStmt<LhsType> stmt, final Void param) {
			return !isClock(stmt.getVarDecl());
		}

		@Override
		public <LhsType extends Type, RhsType extends LhsType> Boolean visit(final AssignStmt<LhsType, RhsType> stmt,
				final Void param) {
			return !isClock(stmt.getVarDecl()) && collectVars(stmt.getExpr()).stream().allMatch(v -> !isClock(v));
		}

		@Override
		public Boolean visit(final AssumeStmt stmt, final Void param) {
			return collectVars(stmt.getCond()).stream().allMatch(v -> !isClock(v));
		}
	}

}
