package hu.bme.mit.theta.analysis.xta;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.List;

import com.google.common.collect.ImmutableList;

import hu.bme.mit.theta.analysis.Action;
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

	public static SyncedXtaAction synced(final List<Loc> sourceLocs, final Edge emitting, final Edge receiving) {
		return new SyncedXtaAction(sourceLocs, emitting, receiving);
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

	}

	public static final class SyncedXtaAction extends XtaAction {
		private final Edge emitting;
		private final Edge receiving;

		private SyncedXtaAction(final List<Loc> source, final Edge emitting, final Edge receiving) {
			super(source);
			this.emitting = checkNotNull(emitting);
			this.receiving = checkNotNull(receiving);
		}

		public Edge getEmitting() {
			return emitting;
		}

		public Edge getReceiving() {
			return receiving;
		}

		@Override
		public List<Loc> getTargetLocs() {
			// TODO Auto-generated method stub
			throw new UnsupportedOperationException("TODO: auto-generated method stub");
		}

		@Override
		public boolean isSynced() {
			return true;
		}

		@Override
		public SyncedXtaAction asSynced() {
			return this;
		}

	}

}
