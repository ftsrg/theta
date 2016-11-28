package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;
import static java.util.Arrays.asList;

import java.util.StringJoiner;
import java.util.function.Function;

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

	public ToStringBuilder addAll(final Iterable<? extends Object> objects) {
		objects.forEach(o -> joiner.add(o.toString()));
		return this;
	}

	public <T> ToStringBuilder addAll(final Iterable<? extends T> objects, final Function<T, String> toStringFunc) {
		objects.forEach(o -> joiner.add(toStringFunc.apply(o)));
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
