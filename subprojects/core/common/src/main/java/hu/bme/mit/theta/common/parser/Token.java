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

import static com.google.common.base.Preconditions.checkNotNull;

public final class Token {
	private static final int HASH_SEED = 4027;
	private volatile int hashCode = 0;

	private final String string;
	private final TokenType type;

	private Token(final String string, final TokenType type) {
		this.string = checkNotNull(string);
		this.type = checkNotNull(type);
	}

	public static Token of(final String string, final TokenType type) {
		return new Token(string, type);
	}

	public TokenType getType() {
		return type;
	}

	public String getString() {
		return string;
	}

	@Override
	public int hashCode() {
		int result = hashCode;
		if (result == 0) {
			result = HASH_SEED;
			result = 31 * result + string.hashCode();
			result = 31 * result + type.hashCode();
			hashCode = result;
		}
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		} else if (obj instanceof Token) {
			final Token that = (Token) obj;
			return this.type.equals(that.type) && this.string.equals(that.string);
		} else {
			return false;
		}
	}

	@Override
	public String toString() {
		return string;
	}

}
