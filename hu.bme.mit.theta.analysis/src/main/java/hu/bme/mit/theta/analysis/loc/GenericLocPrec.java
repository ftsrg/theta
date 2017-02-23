package hu.bme.mit.theta.analysis.loc;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.NoSuchElementException;
import java.util.Optional;

import com.google.common.collect.ImmutableMap;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.ToStringBuilder;
import hu.bme.mit.theta.formalism.common.Edge;
import hu.bme.mit.theta.formalism.common.Loc;

/**
 * Represents an immutable generic precision that can assign a precision to each
 * location.
 */
public final class GenericLocPrec<P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>>
		implements LocPrec<P, L, E> {
	private final Map<L, P> mapping;
	private final Optional<P> defaultPrec;

	private GenericLocPrec(final Map<L, P> mapping, final Optional<P> defaultPrec) {
		this.mapping = mapping;
		this.defaultPrec = defaultPrec;
	}

	public static <P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>> GenericLocPrec<P, L, E> create(
			final Map<L, P> mapping) {
		return new GenericLocPrec<>(ImmutableMap.copyOf(mapping), Optional.empty());
	}

	public static <P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>> GenericLocPrec<P, L, E> create(
			final P defaultPrec) {
		return new GenericLocPrec<P, L, E>(Collections.emptyMap(), Optional.of(defaultPrec));
	}

	public static <P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>> GenericLocPrec<P, L, E> create(
			final Map<L, P> mapping, final P defaultPrec) {
		return new GenericLocPrec<>(ImmutableMap.copyOf(mapping), Optional.of(defaultPrec));
	}

	@Override
	public P getPrec(final L loc) {
		if (mapping.containsKey(loc)) {
			return mapping.get(loc);
		}
		if (defaultPrec.isPresent()) {
			return defaultPrec.get();
		}
		throw new NoSuchElementException("Location not found.");
	}

	public GenericLocPrec<P, L, E> refine(final List<L> locs, final List<P> refinedPrecs) {
		checkNotNull(locs);
		checkNotNull(refinedPrecs);
		checkArgument(locs.size() == refinedPrecs.size());

		final Map<L, P> refinedMapping = new HashMap<>(this.mapping);

		for (int i = 0; i < locs.size(); ++i) {
			refinedMapping.put(locs.get(i), refinedPrecs.get(i));
		}

		return new GenericLocPrec<>(refinedMapping, this.defaultPrec);
	}

	public GenericLocPrec<P, L, E> refine(final L loc, final P refinedPrec) {
		return refine(Collections.singletonList(loc), Collections.singletonList(refinedPrec));
	}

	@Override
	public String toString() {
		final ToStringBuilder builder = ObjectUtils.toStringBuilder(getClass().getSimpleName());
		builder.add("Precs: " + mapping.size());
		if (defaultPrec.isPresent()) {
			builder.add("Default: " + defaultPrec.get());
		}
		return builder.toString();
	}

}
