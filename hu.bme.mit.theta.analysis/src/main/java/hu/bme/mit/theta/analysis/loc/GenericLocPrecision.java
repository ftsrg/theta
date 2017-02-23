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
public final class GenericLocPrecision<P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>>
		implements LocPrec<P, L, E> {
	private final Map<L, P> mapping;
	private final Optional<P> defaultPrecision;

	private GenericLocPrecision(final Map<L, P> mapping, final Optional<P> defaultPrecision) {
		this.mapping = mapping;
		this.defaultPrecision = defaultPrecision;
	}

	public static <P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>> GenericLocPrecision<P, L, E> create(
			final Map<L, P> mapping) {
		return new GenericLocPrecision<>(ImmutableMap.copyOf(mapping), Optional.empty());
	}

	public static <P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>> GenericLocPrecision<P, L, E> create(
			final P defaultPrecision) {
		return new GenericLocPrecision<P, L, E>(Collections.emptyMap(), Optional.of(defaultPrecision));
	}

	public static <P extends Prec, L extends Loc<L, E>, E extends Edge<L, E>> GenericLocPrecision<P, L, E> create(
			final Map<L, P> mapping, final P defaultPrecision) {
		return new GenericLocPrecision<>(ImmutableMap.copyOf(mapping), Optional.of(defaultPrecision));
	}

	@Override
	public P getPrecision(final L loc) {
		if (mapping.containsKey(loc)) {
			return mapping.get(loc);
		}
		if (defaultPrecision.isPresent()) {
			return defaultPrecision.get();
		}
		throw new NoSuchElementException("Location not found.");
	}

	public GenericLocPrecision<P, L, E> refine(final List<L> locs, final List<P> refinedPrecisions) {
		checkNotNull(locs);
		checkNotNull(refinedPrecisions);
		checkArgument(locs.size() == refinedPrecisions.size());

		final Map<L, P> refinedMapping = new HashMap<>(this.mapping);

		for (int i = 0; i < locs.size(); ++i) {
			refinedMapping.put(locs.get(i), refinedPrecisions.get(i));
		}

		return new GenericLocPrecision<>(refinedMapping, this.defaultPrecision);
	}

	public GenericLocPrecision<P, L, E> refine(final L loc, final P refinedPrecision) {
		return refine(Collections.singletonList(loc), Collections.singletonList(refinedPrecision));
	}

	@Override
	public String toString() {
		final ToStringBuilder builder = ObjectUtils.toStringBuilder(getClass().getSimpleName());
		builder.add("Precisions: " + mapping.size());
		if (defaultPrecision.isPresent()) {
			builder.add("Default: " + defaultPrecision.get());
		}
		return builder.toString();
	}

}
