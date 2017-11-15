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

public final class AigerWire {

	private final AigerNode source;
	private final AigerNode target;
	private final boolean isPonated;

	public AigerWire(final AigerNode source, final AigerNode target, final boolean isPonated) {
		this.source = source;
		this.target = target;
		this.isPonated = isPonated;
	}

	public AigerNode getSource() {
		return source;
	}

	public AigerNode getTarget() {
		return target;
	}

	public boolean isPonated() {
		return isPonated;
	}

}
