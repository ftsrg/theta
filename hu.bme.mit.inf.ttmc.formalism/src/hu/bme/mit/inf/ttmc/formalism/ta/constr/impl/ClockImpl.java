package hu.bme.mit.inf.ttmc.formalism.ta.constr.impl;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.inf.ttmc.formalism.common.decl.impl.Decls2.Clock;

import hu.bme.mit.inf.ttmc.formalism.common.decl.ClockDecl;
import hu.bme.mit.inf.ttmc.formalism.ta.constr.Clock;

class ClockImpl implements Clock {

	private static final int HASH_SEED = 9203;

	private final String name;

	private volatile int hashCode = 0;
	private volatile ClockDecl decl = null;

	ClockImpl(final String name) {
		checkNotNull(name);
		checkArgument(name.length() > 0);
		this.name = name;
	}

	@Override
	public String getName() {
		return name;
	}

	@Override
	public ClockDecl asDecl() {
		ClockDecl result = decl;
		if (result == null) {
			result = Clock(name);
			decl = result;
		}
		return result;
	}

	@Override
	public int compareTo(final Clock that) {
		return this.getName().compareTo(that.getName());
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + name.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		return this == obj;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("Clock");
		sb.append("(");
		sb.append(name);
		sb.append(")");
		return sb.toString();
	}

}
