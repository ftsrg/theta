package hu.bme.mit.inf.ttmc.cegar.interpolatingcegar.data;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import hu.bme.mit.inf.ttmc.constraint.ConstraintManager;
import hu.bme.mit.inf.ttmc.constraint.expr.Expr;
import hu.bme.mit.inf.ttmc.constraint.type.BoolType;
import hu.bme.mit.inf.ttmc.constraint.type.Type;

/**
 * Class representing a sequence or binary interpolant. A binary interpolant is
 * a special case of sequence interpolant, where each member of the sequence is
 * 'true' except for the last.
 *
 * @author Akos
 */
public class Interpolant implements Iterable<Expr<? extends BoolType>> {
	private final List<Expr<? extends BoolType>> interpolants; // List of interpolants
	private final boolean isBinary; // Is the interpolant binary

	/**
	 * Constructor (binary)
	 *
	 * @param interpolant
	 *            Interpolant expression
	 * @param index
	 *            Number of 'true' interpolants before the actual one
	 */
	public Interpolant(final Expr<? extends BoolType> interpolant, final int index, final ConstraintManager manager) {
		interpolants = new ArrayList<>();
		for (int i = 0; i < index; ++i)
			interpolants.add(manager.getExprFactory().True());
		interpolants.add(interpolant);
		isBinary = true;
	}

	/**
	 * Constructor (sequence)
	 *
	 * @param interpolants
	 *            Collection of interpolant expressions
	 */
	public Interpolant(final Collection<Expr<? extends BoolType>> interpolants) {
		this.interpolants = new ArrayList<>(interpolants);
		isBinary = false;
	}

	@Override
	public Iterator<Expr<? extends BoolType>> iterator() {
		return interpolants.iterator();
	}

	/**
	 * Get an interpolant expression
	 *
	 * @param index
	 *            Index
	 * @return Interpolant expression at the specified index
	 */
	public Expr<? extends BoolType> get(final int index) {
		return interpolants.get(index);
	}

	public int size() {
		return interpolants.size();
	}

	@Override
	public String toString() {
		if (isBinary) {
			return "[binary] " + interpolants.get(interpolants.size() - 1);
		} else {
			final StringBuilder result = new StringBuilder("[sequence]");
			for (final Expr<? extends Type> e : interpolants)
				result.append(" [").append(e.toString()).append("]");
			return result.toString();
		}
	}
}
