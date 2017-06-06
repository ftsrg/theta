package hu.bme.mit.theta.analysis.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;
import java.util.StringJoiner;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.core.Expr;
import hu.bme.mit.theta.formalism.xta.ChanType;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Edge;
import hu.bme.mit.theta.formalism.xta.XtaProcess.Loc;

public abstract class XtaAction implements Action {

	private final List<Loc> sourceLocs;

	private XtaAction(final List<Loc> source) {
		this.sourceLocs = ImmutableList.copyOf(checkNotNull(source));
	}

	public static SimpleXtaAction simple(final List<Loc> sourceLocs, final Edge edge) {
		return new SimpleXtaAction(sourceLocs, edge);
	}

	public static SyncedXtaAction synced(final List<Loc> sourceLocs, final Expr<ChanType> syncExpr,
			final Edge emittingEdge, final Edge receivingEdge) {
		return new SyncedXtaAction(sourceLocs, syncExpr, emittingEdge, receivingEdge);
	}

	public List<Loc> getSourceLocs() {
		return sourceLocs;
	}

	public abstract List<Loc> getTargetLocs();

	public boolean isSimple() {
		return false;
	}

	public boolean isSynced() {
		return false;
	}

	public SimpleXtaAction asSimple() {
		throw new ClassCastException();
	}

	public SyncedXtaAction asSynced() {
		throw new ClassCastException();
	}

	public static final class SimpleXtaAction extends XtaAction {
		private final Edge edge;
		private final List<Loc> targetLocs;

		private SimpleXtaAction(final List<Loc> sourceLocs, final Edge edge) {
			super(sourceLocs);
			this.edge = checkNotNull(edge);

			final ImmutableList.Builder<Loc> builder = ImmutableList.builder();
			final Loc source = edge.getSource();
			final Loc target = edge.getTarget();
			boolean matched = false;
			for (final Loc loc : sourceLocs) {
				if (loc.equals(source)) {
					checkArgument(!matched);
					builder.add(target);
					matched = true;
				} else {
					builder.add(loc);
				}
			}
			checkArgument(matched);
			targetLocs = builder.build();
		}

		public Edge getEdge() {
			return edge;
		}

		@Override
		public List<Loc> getTargetLocs() {
			return targetLocs;
		}

		@Override
		public boolean isSimple() {
			return true;
		}

		@Override
		public SimpleXtaAction asSimple() {
			return this;
		}

		@Override
		public String toString() {
			final StringJoiner sj = new StringJoiner("\n");
			edge.getGuards().forEach(g -> sj.add("[" + g + "]"));
			edge.getUpdates().forEach(u -> u.toString());
			return sj.toString();
		}

	}

	public static final class SyncedXtaAction extends XtaAction {
		private final Edge emittingEdge;
		private final Edge receivingEdge;
		private final Expr<ChanType> syncExpr;
		private final List<Loc> targetLocs;

		private SyncedXtaAction(final List<Loc> sourceLocs, final Expr<ChanType> syncExpr, final Edge emittingEdge,
				final Edge receivingEdge) {
			super(sourceLocs);
			this.syncExpr = checkNotNull(syncExpr);
			this.emittingEdge = checkNotNull(emittingEdge);
			this.receivingEdge = checkNotNull(receivingEdge);

			final ImmutableList.Builder<Loc> builder = ImmutableList.builder();
			final Loc emittingSource = emittingEdge.getSource();
			final Loc emittingTarget = emittingEdge.getTarget();
			final Loc receivingSource = receivingEdge.getSource();
			final Loc receivingTarget = receivingEdge.getTarget();
			boolean emittingMatched = false;
			boolean receivingMatched = false;
			for (final Loc loc : sourceLocs) {
				if (loc.equals(emittingSource)) {
					checkArgument(!emittingMatched);
					builder.add(emittingTarget);
					emittingMatched = true;
				} else if (loc.equals(receivingSource)) {
					checkArgument(!receivingMatched);
					builder.add(receivingTarget);
					receivingMatched = true;
				} else {
					builder.add(loc);
				}
			}
			checkArgument(emittingMatched);
			checkArgument(receivingMatched);
			targetLocs = builder.build();
		}

		public Expr<ChanType> getSyncExpr() {
			return syncExpr;
		}

		public Edge getEmittingEdge() {
			return emittingEdge;
		}

		public Edge getReceivingEdge() {
			return receivingEdge;
		}

		@Override
		public List<Loc> getTargetLocs() {
			return targetLocs;
		}

		@Override
		public boolean isSynced() {
			return true;
		}

		@Override
		public SyncedXtaAction asSynced() {
			return this;
		}

		@Override
		public String toString() {
			final StringJoiner sj = new StringJoiner("\n");
			sj.add(syncExpr + "!");
			emittingEdge.getGuards().forEach(g -> sj.add("[" + g + "]"));
			receivingEdge.getGuards().forEach(g -> sj.add("[" + g + "]"));
			emittingEdge.getUpdates().forEach(u -> u.toString());
			receivingEdge.getUpdates().forEach(u -> u.toString());
			return sj.toString();
		}

	}

}
