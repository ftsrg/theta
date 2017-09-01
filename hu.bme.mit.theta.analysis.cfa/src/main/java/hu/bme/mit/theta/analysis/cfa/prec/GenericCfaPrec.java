package hu.bme.mit.theta.analysis.cfa.prec;

import static com.google.common.base.Preconditions.checkNotNull;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Optional;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableMap.Builder;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.cfa.CfaPrec;
import hu.bme.mit.theta.common.ObjectUtils;
import hu.bme.mit.theta.common.ToStringBuilder;
import hu.bme.mit.theta.formalism.cfa.CFA.Loc;

/**
 * Represents an immutable generic precision that can assign a precision to each
 * location.
 */
public final class GenericCfaPrec<P extends Prec> implements CfaPrec<P> {
	private final Map<Loc, P> mapping;
	private final Optional<P> defaultPrec;

	private GenericCfaPrec(final Map<Loc, P> mapping, final Optional<P> defaultPrec) {
		this.defaultPrec = defaultPrec;
		final Builder<Loc, P> builder = ImmutableMap.builder();
		for (final Entry<Loc, P> entry : mapping.entrySet()) {
			if (!defaultPrec.isPresent() || !defaultPrec.get().equals(entry.getValue())) {
				builder.put(entry);
			}
		}
		this.mapping = builder.build();
	}

	public static <P extends Prec> GenericCfaPrec<P> create(final Map<Loc, P> mapping) {
		return new GenericCfaPrec<>(mapping, Optional.empty());
	}

	public static <P extends Prec> GenericCfaPrec<P> create(final P defaultPrec) {
		return new GenericCfaPrec<>(Collections.emptyMap(), Optional.of(defaultPrec));
	}

	public static <P extends Prec> GenericCfaPrec<P> create(final Map<Loc, P> mapping, final P defaultPrec) {
		return new GenericCfaPrec<>(mapping, Optional.of(defaultPrec));
	}

	@Override
	public P getPrec(final Loc loc) {
		if (mapping.containsKey(loc)) {
			return mapping.get(loc);
		} else if (defaultPrec.isPresent()) {
			return defaultPrec.get();
		} else {
			throw new NoSuchElementException("Location not found.");
		}
	}

	public GenericCfaPrec<P> refine(final Map<Loc, P> refinedPrecs) {
		checkNotNull(refinedPrecs);

		final Map<Loc, P> refinedMapping = new HashMap<>(this.mapping);

		for (final Entry<Loc, P> entry : refinedPrecs.entrySet()) {
			final Loc loc = entry.getKey();
			final P prec = entry.getValue();

			// TODO: instead of == this should be 'equals' (it is correct this way as well, but it would be more efficient)
			if (defaultPrec.isPresent() && !mapping.containsKey(loc) && defaultPrec.get() == prec) {
				continue;
			}
			refinedMapping.put(loc, prec);
		}

		return new GenericCfaPrec<>(refinedMapping, this.defaultPrec);
	}

	public GenericCfaPrec<P> refine(final Loc loc, final P refinedPrec) {
		return refine(Collections.singletonMap(loc, refinedPrec));
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

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof GenericCfaPrec) {
			final GenericCfaPrec<?> that = (GenericCfaPrec<?>) obj;
			return this.defaultPrec.equals(that.defaultPrec) && this.mapping.equals(that.mapping);
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * (defaultPrec.hashCode() + 13 * mapping.hashCode());
	}
}
