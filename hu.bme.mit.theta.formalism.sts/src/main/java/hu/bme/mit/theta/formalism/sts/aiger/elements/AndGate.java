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

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import com.google.common.collect.ImmutableList;

/**
 * Represents an and gate with exactly two inputs.
 */
public class AndGate extends AigerNode {

	private final List<AigerWire> outWires;
	private AigerWire inWire1;
	private AigerWire inWire2;

	public AndGate(final int nr, final int varId) {
		super(String.format("AND%d_v%d", nr, varId));
		this.outWires = new ArrayList<>();
	}

	@Override
	public Collection<AigerWire> getInWires() {
		return ImmutableList.of(inWire1, inWire2);
	}

	public AigerWire getInWire1() {
		return inWire1;
	}

	public AigerWire getInWire2() {
		return inWire2;
	}

	public void setInWire1(final AigerWire wire) {
		checkArgument(wire.getTarget().equals(this));
		this.inWire1 = wire;
	}

	public void setInWire2(final AigerWire wire) {
		checkArgument(wire.getTarget().equals(this));
		this.inWire2 = wire;
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

	@Override
	public void removeOutWire(final AigerWire outWire) {
		checkArgument(outWires.remove(outWire));
	}

}
