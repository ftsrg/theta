package hu.bme.mit.inf.ttmc.analysis.tcfa;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import hu.bme.mit.inf.ttmc.formalism.common.stmt.Stmt;
import hu.bme.mit.inf.ttmc.formalism.ta.op.ClockOp;
import hu.bme.mit.inf.ttmc.formalism.ta.op.impl.ClockOps;
import hu.bme.mit.inf.ttmc.formalism.tcfa.TCFAEdge;

public abstract class TCFATrans {

	private TCFATrans() {
	}

	public static TCFADelayTrans delay() {
		return TCFADelayTrans.getInstance();
	}

	public static TCFADiscreteTrans discrete(final TCFAEdge edge) {
		checkNotNull(edge);
		return new TCFADiscreteTrans(edge);
	}

	////

	public static final class TCFADelayTrans extends TCFATrans {

		private static final TCFADelayTrans INSTANCE;

		static {
			INSTANCE = new TCFADelayTrans();
		}

		private TCFADelayTrans() {
		}

		private static TCFADelayTrans getInstance() {
			return INSTANCE;
		}

	}

	public static final class TCFADiscreteTrans extends TCFATrans {

		private final TCFAEdge edge;
		private final List<ClockOp> clockOps;
		private final List<Stmt> dataStmts;

		private TCFADiscreteTrans(final TCFAEdge edge) {
			assert edge != null;

			this.edge = edge;
			clockOps = new ArrayList<>();
			dataStmts = new ArrayList<>();
			separateStmts(edge.getStmts());
		}

		public TCFAEdge getEdge() {
			return edge;
		}

		public List<ClockOp> getClockOps() {
			return Collections.unmodifiableList(clockOps);
		}

		public List<Stmt> getDataStmts() {
			return Collections.unmodifiableList(dataStmts);
		}

		private void separateStmts(final List<? extends Stmt> stmts) {
			for (final Stmt stmt : stmts) {
				if (TCFAUtils.isClockStmt(stmt)) {
					clockOps.add(ClockOps.fromStmt(stmt));
				} else if (TCFAUtils.isDataStmt(stmt)) {
					dataStmts.add(stmt);
				} else {
					throw new UnsupportedOperationException();
				}
			}
		}

	}

}
