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
package hu.bme.mit.theta.common;

import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

import java.util.ArrayList;
import java.util.List;
import java.util.StringJoiner;
import java.util.stream.Stream;

import com.google.common.base.Strings;

/**
 * Utility class for printing Lisp style strings, e.g., (A (B 1 2) (C 3)).
 */
public final class LispStringBuilder {
	private static final String LPAREN = "(";
	private static final String RPAREN = ")";
	private static final String SPACE = " ";
	private static final String EOL = System.getProperty("line.separator");

	private final List<Object> headObjs;
	private final List<Object> alignedObjs;
	private final List<Object> bodyObjs;

	private State state;

	private static enum State {
		HEAD, ALIGNED, BODY, BUILT;
	}

	LispStringBuilder(final String prefix) {
		checkNotNull(prefix);
		headObjs = new ArrayList<>();
		alignedObjs = new ArrayList<>();
		bodyObjs = new ArrayList<>();

		if (!"".equals(prefix)) {
			headObjs.add(prefix);
		}

		state = State.HEAD;
	}

	public LispStringBuilder add(final Object object) {
		checkState(state != State.BUILT);
		final List<Object> section = sectionFor(state);
		section.add(object);
		return this;
	}

	public LispStringBuilder addAll(final Iterable<?> iterable) {
		checkState(state != State.BUILT);
		iterable.forEach(this::add);
		return this;
	}

	public LispStringBuilder addAll(final Stream<?> stream) {
		checkState(state != State.BUILT);
		stream.forEach(this::add);
		return this;
	}

	public LispStringBuilder aligned() {
		checkState(state == State.HEAD);
		state = State.ALIGNED;
		return this;
	}

	public LispStringBuilder body() {
		checkState(state == State.HEAD || state == State.ALIGNED);
		state = State.BODY;
		return this;
	}

	@Override
	public String toString() {
		checkState(state != State.BUILT);

		final StringBuilder sb = new StringBuilder();
		sb.append(LPAREN);

		final String head = createHead();
		sb.append(head);

		final int indent = head.length() + 1;
		final String aligned = createAligned(indent);

		sb.append(aligned);

		final String body = createBody();
		sb.append(body);

		sb.append(RPAREN);
		return sb.toString();
	}

	////

	private List<Object> sectionFor(final State state) {
		switch (state) {
			case HEAD:
				return headObjs;
			case ALIGNED:
				return alignedObjs;
			case BODY:
				return bodyObjs;
			default:
				throw new AssertionError("Unhandled state: " + state);
		}
	}

	private String createHead() {
		final StringJoiner sj = new StringJoiner(SPACE);
		for (final Object headObj : headObjs) {
			for (final String line : lines(headObj.toString())) {
				final String trimmedLine = line.trim().replaceAll("( )+", SPACE);
				sj.add(trimmedLine);
			}
		}
		return sj.toString();
	}

	private String createAligned(final int indent) {
		final StringJoiner sj = new StringJoiner(EOL + Strings.repeat(SPACE, indent));
		for (final Object alignedObj : alignedObjs) {
			for (final String line : lines(alignedObj.toString())) {
				sj.add(SPACE + line);
			}
		}
		return sj.toString();
	}

	private String createBody() {
		final StringBuilder sb = new StringBuilder();
		for (final Object bodyObj : bodyObjs) {
			for (final String line : lines(bodyObj.toString())) {
				sb.append(EOL + SPACE + SPACE + line);
			}
		}
		return sb.toString();
	}

	private static String[] lines(final String string) {
		return string.split("\\r\\n|\\n|\\r");
	}

}
