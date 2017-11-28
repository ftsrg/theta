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

public final class FileLogger extends BaseLogger {
	private final PrintWriter pw;
	private final boolean instantFlush;

	public FileLogger(final Level minLevel, final String fileName, final boolean instantFlush, final boolean append)
			throws FileNotFoundException {
		super(minLevel);
		pw = new PrintWriter(new FileOutputStream(fileName, append));
		this.instantFlush = instantFlush;
	}

	public void close() {
		pw.close();
	}

	@Override
	protected void writeStr(final String str) {
		pw.print(str);
		if (instantFlush) {
			pw.flush();
		}
	}

}
