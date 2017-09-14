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
package hu.bme.mit.theta.common.logging.impl;

import java.util.ArrayList;
import java.util.Collection;

import hu.bme.mit.theta.common.logging.Logger;

public final class CompositeLogger implements Logger {
	private final Collection<Logger> loggers;

	public CompositeLogger(final Logger[] loggers) {
		this.loggers = new ArrayList<>(loggers.length);
		for (int i = 0; i < loggers.length; ++i)
			this.loggers.add(loggers[i]);
	}

	public CompositeLogger(final Collection<Logger> loggers) {
		this.loggers = new ArrayList<>(loggers);
	}

	@Override
	public Logger write(final Object obj, final int level, final int padding) {
		for (final Logger logger : loggers)
			logger.write(obj, level, padding);
		return this;
	}

	@Override
	public Logger writeln(final int level) {
		for (final Logger logger : loggers)
			logger.writeln(level);
		return this;
	}

	@Override
	public Logger writeHeader(final Object obj, final int level) {
		for (final Logger logger : loggers)
			logger.writeHeader(obj, level);
		return this;
	}

}
