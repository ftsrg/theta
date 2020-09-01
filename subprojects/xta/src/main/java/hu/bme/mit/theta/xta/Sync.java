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
package hu.bme.mit.theta.xta;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.Type;

import java.util.List;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.Streams.zip;
import static hu.bme.mit.theta.xta.Sync.Kind.EMIT;
import static hu.bme.mit.theta.xta.Sync.Kind.RECV;

public final class Sync {

	private static final int HASH_SEED = 6547;

	private volatile int hashCode = 0;

	public enum Kind {
		EMIT, RECV
	}

	private final Label label;
	private final List<Expr<?>> args;
	private final Kind kind;

	private Sync(final Label label, final List<? extends Expr<?>> args, final Kind kind) {
		checkNotNull(label);
		checkNotNull(args);
		checkNotNull(kind);
		final List<Type> types = label.getParamTypes();
		checkArgument(args.size() == types.size());
		checkArgument(zip(args.stream(), types.stream(), (a, t) -> a.getType() == t).allMatch(p -> p));
		this.label = label;
		this.args = ImmutableList.copyOf(args);
		this.kind = kind;
	}

	public static Sync emit(final Label label, final List<? extends Expr<?>> args) {
		return new Sync(label, args, EMIT);
	}

	public static Sync recv(final Label label, final List<? extends Expr<?>> args) {
		return new Sync(label, args, RECV);
	}

	public Label getLabel() {
		return label;
	}

	public List<Expr<?>> getArgs() {
		return args;
	}

	public Kind getKind() {
		return kind;
	}

	public boolean mayReceive(final Sync that) {
		checkArgument(that.kind.equals(EMIT));
		return this.label.equals(that.label) && this.kind.equals(RECV);
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + label.hashCode();
			result = 31 * result + args.hashCode();
			result = 31 * result + kind.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof Sync) {
			final Sync that = (Sync) obj;
			return this.label.equals(that.label) && this.kind.equals(that.kind) && this.args.equals(that.args);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return Utils.lispStringBuilder(label.getName()).add(kind == EMIT ? "!" : "?").addAll(args).toString();
	}

}
