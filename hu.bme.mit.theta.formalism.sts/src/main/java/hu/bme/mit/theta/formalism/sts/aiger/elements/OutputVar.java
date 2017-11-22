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
package hu.bme.mit.theta.formalism.sts.aiger.elements;

import static com.google.common.base.Preconditions.checkArgument;

import java.util.Collection;
import java.util.Collections;

/**
 * Represents an output variable.
 */
public class OutputVar extends AigerNode {

	private AigerWire inWire;

	public OutputVar(final int nr) {
		super(String.format("OUT%d", nr));
	}

	@Override
	public Collection<AigerWire> getInWires() {
		return Collections.singleton(inWire);
	}

	public AigerWire getInWire() {
		return inWire;
	}

	public void setInWire(final AigerWire wire) {
		checkArgument(wire.getTarget().equals(this));
		this.inWire = wire;
	}

	@Override
	public Collection<AigerWire> getOutWires() {
		return Collections.emptyList();
	}

	@Override
	public void addOutWire(final AigerWire outWire) {
		throw new UnsupportedOperationException("Output variables cannot have outgoing wires.");
	}

	@Override
	public void removeOutWire(final AigerWire outWire) {
		throw new UnsupportedOperationException("Output variables cannot have outgoing wires.");
	}

}
