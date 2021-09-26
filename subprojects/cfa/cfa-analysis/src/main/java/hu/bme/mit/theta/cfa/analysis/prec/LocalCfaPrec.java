/*
 *  Copyright 2017 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */
package hu.bme.mit.theta.cfa.analysis.prec;

import com.google.common.collect.ImmutableMap;
import com.google.common.collect.ImmutableMap.Builder;
import com.google.common.collect.Streams;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.cfa.CFA.Loc;
import hu.bme.mit.theta.cfa.analysis.CfaPrec;
import hu.bme.mit.theta.common.LispStringBuilder;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;

import java.util.Collection;
import java.util.Collections;
import java.util.Map;
import java.util.Map.Entry;
import java.util.NoSuchElementException;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

/**
 * Represents an immutable local precision that can assign a precision to each
 * location. A refiner is also implemented.
 *
 * @see LocalCfaPrecRefiner
 */
public final class LocalCfaPrec<P extends Prec> implements CfaPrec<P> {
	private final Map<Loc, P> mapping;
	private final Optional<P> defaultPrec;

	private LocalCfaPrec(final Map<Loc, P> mapping, final Optional<P> defaultPrec) {
		this.defaultPrec = defaultPrec;
		final Builder<Loc, P> builder = ImmutableMap.builder();
		for (final Entry<Loc, P> entry : mapping.entrySet()) {
			if (!defaultPrec.isPresent() || !defaultPrec.get().equals(entry.getValue())) {
				builder.put(entry);
			}
		}
		this.mapping = builder.build();
	}

	public static <P extends Prec> LocalCfaPrec<P> create(final Map<Loc, P> mapping) {
		return new LocalCfaPrec<>(mapping, Optional.empty());
	}

	public static <P extends Prec> LocalCfaPrec<P> create(final P defaultPrec) {
		return new LocalCfaPrec<>(Collections.emptyMap(), Optional.of(defaultPrec));
	}

	public static <P extends Prec> LocalCfaPrec<P> create(final Map<Loc, P> mapping, final P defaultPrec) {
		return new LocalCfaPrec<>(mapping, Optional.of(defaultPrec));
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

	public LocalCfaPrec<P> refine(final Map<Loc, P> refinedPrecs) {
		checkNotNull(refinedPrecs);

		final Map<Loc, P> refinedMapping = Containers.createMap(this.mapping);

		for (final Entry<Loc, P> entry : refinedPrecs.entrySet()) {
			final Loc loc = entry.getKey();
			final P prec = entry.getValue();

			// TODO: instead of == this should be 'equals' (it is correct this
			// way as well, but it would be more efficient)
			if (defaultPrec.isPresent() && !mapping.containsKey(loc) && defaultPrec.get() == prec) {
				continue;
			}
			refinedMapping.put(loc, prec);
		}

		return new LocalCfaPrec<>(refinedMapping, this.defaultPrec);
	}

	public LocalCfaPrec<P> refine(final Loc loc, final P refinedPrec) {
		return refine(Collections.singletonMap(loc, refinedPrec));
	}

	@Override
	public String toString() {
		final LispStringBuilder builder = Utils.lispStringBuilder(getClass().getSimpleName());
		if (defaultPrec.isPresent()) {
			builder.add(Utils.lispStringBuilder("default").add(defaultPrec.get()).toString());
		}
		mapping.entrySet().forEach(e -> builder.add(Utils.lispStringBuilder(e.getKey() + "").add(e.getValue())));
		return builder.toString();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof LocalCfaPrec) {
			final LocalCfaPrec<?> that = (LocalCfaPrec<?>) obj;
			return this.defaultPrec.equals(that.defaultPrec) && this.mapping.equals(that.mapping);
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return 31 * (defaultPrec.hashCode() + 13 * mapping.hashCode());
	}

	@Override
	public Collection<VarDecl<?>> getUsedVars() {
		return mapping.values().stream().map(Prec::getUsedVars).reduce((varDecls, varDecls2) -> Streams.concat(varDecls.stream(), varDecls2.stream()).collect(Collectors.toSet())).orElse(Set.of());
	}
}
