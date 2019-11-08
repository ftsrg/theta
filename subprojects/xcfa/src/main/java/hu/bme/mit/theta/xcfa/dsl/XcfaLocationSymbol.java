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
package hu.bme.mit.theta.xcfa.dsl;

import hu.bme.mit.theta.xcfa.XCFA;
import hu.bme.mit.theta.xcfa.dsl.gen.XcfaDslParser.LocContext;

import java.util.HashMap;
import java.util.Map;

import static com.google.common.base.Preconditions.checkNotNull;

final class XcfaLocationSymbol extends InstantiatableSymbol<XCFA.Process.Procedure.Location> {

	private final boolean init;
	private final boolean finall;
	private final boolean error;
	private final String name;
	private final Map<String, String> dictionary;
	private XCFA.Process.Procedure.Location loc = null;

	XcfaLocationSymbol(final LocContext context) {
		checkNotNull(context);
		init = (context.init != null);
		finall = (context.finall != null);
		error = (context.error != null);
		name = context.id.getText();
		dictionary = new HashMap<>();
	}

	@Override
	public String getName() {
		return name;
	}

	public boolean isInit() {
		return init;
	}

	public boolean isFinal() {
		return finall;
	}

	public boolean isError() {
		return error;
	}

	public XCFA.Process.Procedure.Location instantiate() {
		if (loc != null) return loc;
		return loc = new XCFA.Process.Procedure.Location(name, dictionary);
	}

	void addDictionaryEntry(final String key, final String value) {
		dictionary.put(key, value);
	}

	public Map<String, String> getDictionary() {
		return dictionary;
	}
}
