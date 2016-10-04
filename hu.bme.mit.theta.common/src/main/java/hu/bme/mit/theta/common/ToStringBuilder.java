package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Arrays.asList;

import java.util.Collection;
import java.util.StringJoiner;

public final class ToStringBuilder {

	private final StringJoiner joiner;

	ToStringBuilder(final String prefix) {
		checkNotNull(prefix);
		joiner = new StringJoiner(", ", prefix + "(", ")");
	}

	public ToStringBuilder add(final Object object) {
		joiner.add(object.toString());
		return this;
	}

	public ToStringBuilder addAll(final Collection<? extends Object> objects) {
		objects.forEach(o -> joiner.add(o.toString()));
		return this;
	}

	public ToStringBuilder addAll(final Object... objects) {
		addAll(asList(objects));
		return this;
	}

	@Override
	public String toString() {
		return joiner.toString();
	}

}
