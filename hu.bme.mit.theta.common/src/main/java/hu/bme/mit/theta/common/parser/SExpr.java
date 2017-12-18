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
package hu.bme.mit.theta.common.parser;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.collect.ImmutableList.toImmutableList;
import static com.google.common.collect.Streams.stream;
import static java.util.stream.Collectors.joining;

import java.io.Reader;
import java.io.StringReader;
import java.util.Iterator;
import java.util.List;

import com.google.common.collect.ImmutableList;

public abstract class SExpr {

	private SExpr() {
	}

	public static SAtom atom(final String atom) {
		return new SAtom(atom);
	}

	public static SList list(final Iterable<? extends SExpr> sexprs) {
		return new SList(sexprs);
	}

	public static SList list(final SExpr... sexprs) {
		return list(ImmutableList.copyOf(sexprs));
	}

	public static SExpr build(final Object object) {
		checkNotNull(object);
		if (object instanceof String) {
			final String string = (String) object;
			return atom(string);
		} else if (object instanceof Iterable) {
			final Iterable<?> iterable = (Iterable<?>) object;
			final List<SExpr> sexprs = stream(iterable).map(SExpr::build).collect(toImmutableList());
			return list(sexprs);
		} else {
			throw new IllegalArgumentException(
					"Only String and Iterable types are supported, found: " + object.getClass().getSimpleName());
		}
	}

	public static SExpr parse(final String string) {
		checkNotNull(string);
		final Reader reader = new StringReader(string);
		final LispLexer lexer = new LispLexer(reader);
		final LispParser parser = new LispParser(lexer);
		return parser.sexpr();
	}

	public boolean isAtom() {
		return false;
	}

	public boolean isList() {
		return false;
	}

	public SAtom asAtom() {
		throw new ClassCastException();
	}

	public SList asList() {
		throw new ClassCastException();
	}

	public static final class SAtom extends SExpr {
		private static final int HASH_SEED = 3943;
		private volatile int hashCode = 0;

		private final String string;

		private SAtom(final String string) {
			checkNotNull(string);
			checkArgument(string.length() > 0);
			this.string = string;
		}

		@Override
		public boolean isAtom() {
			return true;
		}

		@Override
		public SAtom asAtom() {
			return this;
		}

		@Override
		public int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 31 * result + string.hashCode();
				hashCode = result;
			}
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj instanceof SAtom) {
				final SAtom that = (SAtom) obj;
				return this.string.equals(that.string);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			return string;
		}
	}

	public static final class SList extends SExpr implements Iterable<SExpr> {
		private static final String LPAREN = "(";
		private static final String RPAREN = ")";
		private static final String SPACE = " ";

		private static final int HASH_SEED = 6563;
		private volatile int hashCode = 0;

		private final List<SExpr> list;

		private SList(final Iterable<? extends SExpr> sexprs) {
			checkNotNull(sexprs);
			this.list = ImmutableList.copyOf(sexprs);
		}

		public List<SExpr> getList() {
			return list;
		}

		@Override
		public boolean isList() {
			return true;
		}

		@Override
		public SList asList() {
			return this;
		}

		@Override
		public Iterator<SExpr> iterator() {
			return list.iterator();
		}

		@Override
		public int hashCode() {
			int result = hashCode;
			if (result == 0) {
				result = HASH_SEED;
				result = 31 * result + list.hashCode();
				hashCode = result;
			}
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			} else if (obj instanceof SList) {
				final SList that = (SList) obj;
				return this.list.equals(that.list);
			} else {
				return false;
			}
		}

		@Override
		public String toString() {
			return list.stream().map(Object::toString).collect(joining(SPACE, LPAREN, RPAREN));
		}
	}

}
