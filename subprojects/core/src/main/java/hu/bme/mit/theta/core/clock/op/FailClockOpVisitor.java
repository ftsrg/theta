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
package hu.bme.mit.theta.core.clock.op;

public class FailClockOpVisitor<P, R> implements ClockOpVisitor<P, R> {

	@Override
	public R visit(final CopyOp op, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final FreeOp op, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final GuardOp op, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final ResetOp op, final P param) {
		throw new UnsupportedOperationException();
	}

	@Override
	public R visit(final ShiftOp op, final P param) {
		throw new UnsupportedOperationException();
	}

}
