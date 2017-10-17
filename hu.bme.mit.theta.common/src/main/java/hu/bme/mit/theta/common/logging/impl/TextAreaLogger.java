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

import hu.bme.mit.theta.common.logging.Logger;
import javafx.application.Platform;
import javafx.scene.control.TextArea;

public final class TextAreaLogger extends MinLevelBasedLogger {
	private final TextArea textArea;

	public TextAreaLogger(final int minLevel, final TextArea textArea) {
		super(minLevel);
		this.textArea = textArea;
	}

	@Override
	public Logger write(final Object obj, final int level, final int padding) {
		if (level <= minLevel) {
			for (int i = 0; i < padding; ++i) {
				appendText("|   ");
			}
			appendText(obj.toString());

		}
		return this;
	}

	@Override
	public Logger writeln(final int level) {
		if (level <= minLevel) {
			appendText(System.lineSeparator());
		}
		return this;
	}

	@Override
	public Logger writeHeader(final Object obj, final int level) {
		if (level <= minLevel) {
			appendText(System.lineSeparator());
			appendText("----------" + obj + "----------");
			appendText(System.lineSeparator());
		}
		return this;
	}

	private void appendText(final String text) {
		Platform.runLater(() -> textArea.appendText(text));
	}

}
