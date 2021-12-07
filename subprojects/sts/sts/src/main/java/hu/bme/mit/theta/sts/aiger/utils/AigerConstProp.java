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

package hu.bme.mit.theta.sts.aiger.utils;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import hu.bme.mit.theta.sts.aiger.elements.AigerNode;
import hu.bme.mit.theta.sts.aiger.elements.AigerSystem;
import hu.bme.mit.theta.sts.aiger.elements.AigerWire;
import hu.bme.mit.theta.sts.aiger.elements.AndGate;
import hu.bme.mit.theta.sts.aiger.elements.FalseConst;
import hu.bme.mit.theta.sts.aiger.elements.Latch;

/**
 * Constant propagation for AIGER systems.
 */
public final class AigerConstProp {

	private AigerConstProp() {
	}

	/**
	 * Propagate constants in an AIGER system. The parameter is modified. It is
	 * assumed that the system contains a single constant.
	 *
	 * @param system
	 */
	public static void apply(final AigerSystem system) {
		final Optional<AigerNode> falseOpt = system.getNodes().stream().filter(n -> n instanceof FalseConst)
				.findFirst();
		if (!falseOpt.isPresent()) {
			return;
		}
		final FalseConst falseConst = (FalseConst) falseOpt.get();
		while (propagateAnd(system, falseConst) || propagateLatch(system, falseConst)) {
		}
	}

	/**
	 * Propagate a constant through an AND gate using (true AND x == x), (false
	 * AND x == false).
	 *
	 * @return True, if any propagation occurred
	 */
	private static boolean propagateAnd(final AigerSystem system, final FalseConst falseConst) {
		final Optional<AigerWire> wireOpt = falseConst.getOutWires().stream()
				.filter(w -> w.getTarget() instanceof AndGate).findFirst();
		if (wireOpt.isPresent()) {
			final AigerWire wire = wireOpt.get();
			final AndGate andGate = (AndGate) wire.getTarget();
			final AigerWire otherWire = andGate.getInWire1().equals(wire) ? andGate.getInWire2() : andGate.getInWire1();
			final AigerNode otherSource = otherWire.getSource();
			otherSource.getOutWires().remove(otherWire);
			final List<AigerWire> redirectedWires = new ArrayList<>();
			redirectedWires.addAll(andGate.getOutWires());
			if (wire.isPonated()) {
				redirectedWires.forEach(w -> w.modifySource(falseConst));
			} else {
				redirectedWires.forEach(w -> w.modifySource(otherSource));
				if (!otherWire.isPonated()) {
					redirectedWires.forEach(w -> w.invert());
				}
			}
			system.getNodes().remove(andGate);
			falseConst.getOutWires().remove(wire);
			return true;
		} else {
			return false;
		}
	}

	/**
	 * Propagate a false constant through a latch. Note, that true constants
	 * cannot be propagated this way, as the initial state of the latch is
	 * false.
	 *
	 * @return True, if any propagation occurred
	 */
	private static boolean propagateLatch(final AigerSystem system, final FalseConst falseConst) {
		final Optional<AigerWire> wireOpt = falseConst.getOutWires().stream()
				.filter(w -> w.getTarget() instanceof Latch && w.isPonated()).findFirst();
		if (wireOpt.isPresent()) {
			final AigerWire wire = wireOpt.get();
			final Latch latch = (Latch) wire.getTarget();
			final List<AigerWire> redirectedWires = new ArrayList<>();
			redirectedWires.addAll(latch.getOutWires());
			redirectedWires.forEach(w -> w.modifySource(falseConst));
			system.getNodes().remove(latch);
			falseConst.getOutWires().remove(wire);
			return true;
		} else {
			return false;
		}
	}
}
