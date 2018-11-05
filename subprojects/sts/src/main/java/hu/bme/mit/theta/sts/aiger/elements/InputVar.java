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
package hu.bme.mit.theta.sts.aiger.elements;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;

/**
 * Represents an input variable.
 */
public final class InputVar extends AigerNode {
	private final Collection<AigerWire> outWires;

	public InputVar(final int nr, final int varId) {
		super(String.format("IN%d_v%d", nr, varId));
		this.outWires = new ArrayList<>();
	}

	@Override
	public Collection<AigerWire> getInWires() {
		return Collections.emptyList();
	}

	@Override
	public Collection<AigerWire> getOutWires() {
		return outWires;
	}

	@Override
	public void addOutWire(final AigerWire outWire) {
		checkArgument(outWire.getSource().equals(this));
		outWires.add(outWire);
	}
}
