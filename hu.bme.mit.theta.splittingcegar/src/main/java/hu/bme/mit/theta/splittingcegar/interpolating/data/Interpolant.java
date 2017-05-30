package hu.bme.mit.theta.splittingcegar.interpolating.data;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.True;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

import hu.bme.mit.theta.core.expr.Expr;
import hu.bme.mit.theta.core.type.BoolType;
import hu.bme.mit.theta.core.type.Type;

/**
 * Class representing a sequence or binary interpolant. A binary interpolant is
 * a special case of sequence interpolant, where each member of the sequence is
 * 'true' except for the last.
 */
public class Interpolant implements Iterable<Expr<? extends BoolType>> {
	private final List<Expr<? extends BoolType>> interpolants;
	private final boolean isBinary;

	public Interpolant(final Expr<? extends BoolType> binaryItp, final int index) {
		checkNotNull(binaryItp);
		checkArgument(0 <= index);
		interpolants = new ArrayList<>();
		for (int i = 0; i < index; ++i)
			interpolants.add(True());
		interpolants.add(binaryItp);
		isBinary = true;
	}

	public Interpolant(final Collection<Expr<? extends BoolType>> seqenceItp) {
		this.interpolants = new ArrayList<>(seqenceItp);
		isBinary = false;
	}

	@Override
	public Iterator<Expr<? extends BoolType>> iterator() {
		return interpolants.iterator();
	}

	public Expr<? extends BoolType> get(final int index) {
		checkArgument(0 <= index && index < interpolants.size());
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
