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

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;

import hu.bme.mit.theta.common.logging.Logger;

public final class FileLogger extends MinLevelBasedLogger {
	private final PrintWriter pw;
	private final boolean instantFlush;

	public FileLogger(final int minLevel, final String fileName, final boolean instantFlush, final boolean append)
			throws FileNotFoundException {
		super(minLevel);
		pw = new PrintWriter(new FileOutputStream(fileName, append));
		this.instantFlush = instantFlush;
	}

	@Override
	public Logger write(final Object obj, final int level, final int padding) {
		if (level <= minLevel) {
			for (int i = 0; i < padding; ++i)
				pw.print("   ");
			pw.print(obj);
			if (instantFlush)
				pw.flush();
		}
		return this;
	}

	@Override
	public Logger writeln(final int level) {
		if (level <= minLevel) {
			pw.println();
			if (instantFlush)
				pw.flush();
		}
		return this;
	}

	@Override
	public Logger writeHeader(final Object obj, final int level) {
		if (level <= minLevel) {
			pw.println();
			pw.println("----------" + obj + "----------");
			if (instantFlush)
				pw.flush();
		}
		return this;
	}

	public void close() {
		pw.close();
	}

}
