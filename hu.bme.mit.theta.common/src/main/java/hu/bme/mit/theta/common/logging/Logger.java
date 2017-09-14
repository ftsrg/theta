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
package hu.bme.mit.theta.common.logging;

public interface Logger {
	default Logger write(final Object obj, final int level) {
		write(obj, level, 0);
		return this;
	}

	Logger write(Object obj, int level, int padding);

	Logger writeln(int level);

	default Logger writeln(final Object obj, final int level) {
		writeln(obj, level, 0);
		return this;
	}

	default Logger writeln(final Object obj, final int level, final int padding) {
		write(obj, level, padding);
		writeln(level);
		return this;
	}

	default Logger writeln(final Object o1, final Object o2, final int level, final int padding) {
		write(o1, level, padding);
		write(o2, level);
		writeln(level);
		return this;
	}

	Logger writeHeader(Object obj, int level);
}
