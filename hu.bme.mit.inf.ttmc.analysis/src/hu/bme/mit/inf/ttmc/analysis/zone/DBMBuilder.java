package hu.bme.mit.inf.ttmc.analysis.zone;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Inf;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Leq;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.Lt;
import static hu.bme.mit.inf.ttmc.analysis.zone.DiffBounds.add;
import static java.lang.Math.max;
import static java.lang.Math.min;

import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.Map;

import hu.bme.mit.inf.ttmc.common.matrix.IntMatrix;
import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.AndConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.ClockConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.DiffLtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.TrueConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitEqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitGtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLeqConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.UnitLtConstr;
import hu.bme.mit.inf.ttmc.formalism.ta.utils.ClockConstrVisitor;

public final class DBMBuilder {

	final LinkedHashMap<ClockDecl, Integer> clockToIndex;

	int nClocks;
	final IntMatrix matrix;

	private final AndOperationVisitor visitor;

	DBMBuilder(final Collection<? extends ClockDecl> clocks) {
		clockToIndex = createIndexMapFrom(clocks);
		nClocks = clockToIndex.size() - 1;
		matrix = IntMatrix.create(nClocks + 1, nClocks + 1);
		matrix.fill((i, j) -> i == 0 || i == j ? Leq(0) : Inf());
		visitor = new AndOperationVisitor();
	}

	DBMBuilder(final Map<ClockDecl, Integer> clockToIndex, final IntMatrix matrix) {
		this.clockToIndex = new LinkedHashMap<>(clockToIndex);
		nClocks = clockToIndex.size() - 1;
		this.matrix = IntMatrix.copyOf(matrix);
		visitor = new AndOperationVisitor();
	}

	public DBM build() {
		return new DBM(this);
	}

	////

	public DBMBuilder track(final ClockDecl clock) {
		Integer index = clockToIndex.get(clock);
		if (index == null) {
			nClocks = nClocks + 1;
			index = nClocks;

			clockToIndex.put(clock, index);
			matrix.expand(nClocks + 1, nClocks + 1);

			final int x = index;
			matrix.set(0, x, Leq(0));
			matrix.set(x, x, Leq(0));
			matrix.set(x, 0, Inf());
			for (int i = 1; i <= nClocks - 1; i++) {
				matrix.set(x, i, Inf());
				matrix.set(i, x, matrix.get(i, 0));
			}
		}
		return this;
	}

	public DBMBuilder untrack(final ClockDecl clock) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	//

	public DBMBuilder up() {
		for (int i = 1; i <= nClocks; i++) {
			matrix.set(i, 0, Inf());
		}
		assert isClosed();
		return this;
	}

	public DBMBuilder down() {
		for (int i = 1; i <= nClocks; i++) {
			matrix.set(0, i, Leq(0));
			for (int j = 1; j <= nClocks; j++) {
				if (matrix.get(j, i) < matrix.get(0, i)) {
					matrix.set(0, i, matrix.get(j, i));
				}
			}
		}
		assert isClosed();
		return this;
	}

	//

	public DBMBuilder and(final ClockConstr constr) {
		checkNotNull(constr);

		constr.accept(visitor, null);
		return this;
	}

	//

	public DBMBuilder free(final ClockDecl clock) {
		checkNotNull(clock);
		checkNotZeroClock(clock);

		final int x = indexOf(clock);
		free(x);

		return this;
	}

	private void free(final int x) {
		for (int i = 0; i <= nClocks; i++) {
			if (i != x) {
				matrix.set(x, i, Inf());
				matrix.set(i, x, matrix.get(i, 0));
			}
		}
		assert isClosed();
	}

	//

	public DBMBuilder reset(final ClockDecl clock, final int m) {
		checkNotNull(clock);
		checkNotZeroClock(clock);

		final int x = indexOf(clock);
		reset(x, m);

		return this;
	}

	private void reset(final int x, final int m) {
		for (int i = 0; i <= nClocks; i++) {
			matrix.set(x, i, add(Leq(m), matrix.get(0, i)));
			matrix.set(i, x, add(matrix.get(i, 0), Leq(-m)));
		}
		assert isClosed();
	}

	//

	public DBMBuilder copy(final ClockDecl lhs, final ClockDecl rhs) {
		checkNotNull(lhs);
		checkNotNull(rhs);
		checkNotZeroClock(lhs);
		checkNotZeroClock(rhs);

		final int x = indexOf(lhs);
		final int y = indexOf(rhs);
		copy(x, y);

		return this;
	}

	private void copy(final int x, final int y) {
		for (int i = 0; i <= nClocks; i++) {
			if (i != x) {
				matrix.set(x, i, matrix.get(y, i));
				matrix.set(i, x, matrix.get(i, y));
			}
		}
		matrix.set(x, y, Leq(0));
		matrix.set(y, x, Leq(0));
		assert isClosed();
	}

	//

	public DBMBuilder shift(final ClockDecl clock, final int m) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@SuppressWarnings("unused")
	private void shift(final int x, final int m) {
		for (int i = 0; i <= nClocks; i++) {
			if (i != x) {
				matrix.set(x, i, add(matrix.get(x, i), Leq(m)));
				matrix.set(i, x, add(matrix.get(i, x), Leq(-m)));
			}
		}
		matrix.set(x, 0, max(matrix.get(x, 0), Leq(0)));
		matrix.set(0, x, min(matrix.get(0, x), Leq(0)));
		assert isClosed();
	}

	//

	public DBMBuilder norm(final Map<ClockDecl, Integer> bounds) {
		// TODO Auto-generated method stub
		throw new UnsupportedOperationException("TODO: auto-generated method stub");
	}

	@SuppressWarnings("unused")
	private void norm(final int[] k) {
		for (int i = 0; i <= nClocks; i++) {
			for (int j = 0; j <= nClocks; j++) {
				if (matrix.get(i, j) != Inf()) {
					if (matrix.get(i, j) > Leq(k[i])) {
						matrix.set(i, j, Inf());
					} else if (matrix.get(i, j) < Leq(-k[j])) {
						matrix.set(i, j, Lt(-k[j]));
					}
				}
			}
		}
		close();
	}

	private void close() {
		for (int k = 0; k <= nClocks; k++) {
			for (int i = 0; i <= nClocks; i++) {
				for (int j = 0; j <= nClocks; j++) {
					matrix.set(i, j, min(matrix.get(i, j), add(matrix.get(i, k), matrix.get(k, j))));
				}
			}
		}
		assert isClosed();
	}

	////

	private boolean isTracked(final ClockDecl clock) {
		return clockToIndex.containsKey(clock);
	}

	private int indexOf(final ClockDecl clock) {
		checkArgument(isTracked(clock));
		return clockToIndex.get(clock);
	}

	private boolean isClosed() {
		for (int i = 0; i <= nClocks; i++) {
			for (int j = 0; j <= nClocks; j++) {
				for (int k = 0; k <= nClocks; k++) {
					if (matrix.get(i, j) > add(matrix.get(i, k), matrix.get(k, j))) {
						return false;
					}
				}
			}
		}
		return true;
	}

	private static void checkNotZeroClock(final ClockDecl clock) {
		checkArgument(!clock.equals(DBM.ZERO_CLOCK));
	}

	private static LinkedHashMap<ClockDecl, Integer> createIndexMapFrom(final Collection<? extends ClockDecl> clocks) {
		final LinkedHashMap<ClockDecl, Integer> result = new LinkedHashMap<ClockDecl, Integer>();
		result.put(DBM.ZERO_CLOCK, 0);
		int i = 1;
		for (final ClockDecl clock : clocks) {
			if (!result.containsKey(clock)) {
				result.put(clock, i);
				i++;
			}
		}
		return result;
	}

	////

	private final class AndOperationVisitor implements ClockConstrVisitor<Void, Void> {

		private void and(final int x, final int y, final int b) {
			if (add(matrix.get(y, x), b) < 0) {
				matrix.set(0, 0, Leq(-1));

			} else if (b < matrix.get(x, y)) {
				matrix.set(x, y, b);

				for (int i = 0; i <= nClocks; i++) {
					for (int j = 0; j <= nClocks; j++) {
						if (add(matrix.get(i, x), matrix.get(x, j)) < matrix.get(i, j)) {
							matrix.set(i, j, add(matrix.get(i, x), matrix.get(x, j)));
						}
						if (add(matrix.get(i, y), matrix.get(y, j)) < matrix.get(i, j)) {
							matrix.set(i, j, add(matrix.get(i, y), matrix.get(y, j)));
						}
					}
				}
			}
			assert isClosed();
		}

		@Override
		public Void visit(final TrueConstr constr, final Void param) {
			return null;
		}

		@Override
		public Void visit(final UnitLtConstr constr, final Void param) {
			final int x = indexOf(constr.getClock());
			final int m = constr.getBound();
			and(x, 0, Lt(m));
			return null;
		}

		@Override
		public Void visit(final UnitLeqConstr constr, final Void param) {
			final int x = indexOf(constr.getClock());
			final int m = constr.getBound();
			and(x, 0, Leq(m));
			return null;
		}

		@Override
		public Void visit(final UnitGtConstr constr, final Void param) {
			final int x = indexOf(constr.getClock());
			final int m = constr.getBound();
			and(0, x, Lt(-m));
			return null;
		}

		@Override
		public Void visit(final UnitGeqConstr constr, final Void param) {
			final int x = indexOf(constr.getClock());
			final int m = constr.getBound();
			and(0, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final UnitEqConstr constr, final Void param) {
			final int x = indexOf(constr.getClock());
			final int m = constr.getBound();
			and(x, 0, Leq(m));
			and(0, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final DiffLtConstr constr, final Void param) {
			final int x = indexOf(constr.getLeftClock());
			final int y = indexOf(constr.getRightClock());
			final int m = constr.getBound();
			and(x, y, Lt(m));
			return null;
		}

		@Override
		public Void visit(final DiffLeqConstr constr, final Void param) {
			final int x = indexOf(constr.getLeftClock());
			final int y = indexOf(constr.getRightClock());
			final int m = constr.getBound();
			and(x, y, Leq(m));
			return null;
		}

		@Override
		public Void visit(final DiffGtConstr constr, final Void param) {
			final int x = indexOf(constr.getLeftClock());
			final int y = indexOf(constr.getRightClock());
			final int m = constr.getBound();
			and(y, x, Lt(-m));
			return null;
		}

		@Override
		public Void visit(final DiffGeqConstr constr, final Void param) {
			final int x = indexOf(constr.getLeftClock());
			final int y = indexOf(constr.getRightClock());
			final int m = constr.getBound();
			and(y, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final DiffEqConstr constr, final Void param) {
			final int x = indexOf(constr.getLeftClock());
			final int y = indexOf(constr.getRightClock());
			final int m = constr.getBound();
			and(x, y, Leq(m));
			and(y, x, Leq(-m));
			return null;
		}

		@Override
		public Void visit(final AndConstr constr, final Void param) {
			for (final ClockConstr atomicConstr : constr.getConstrs()) {
				atomicConstr.accept(this, param);
				if (matrix.get(0, 0) < 0) {
					return null;
				}
			}
			return null;
		}
	}

}
