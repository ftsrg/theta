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
package hu.bme.mit.theta.xta;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.core.clock.op.ClockOp;
import hu.bme.mit.theta.core.clock.op.ClockOps;
import hu.bme.mit.theta.core.stmt.Stmt;

public abstract class Update {

	private Update() {
	}

	static DataUpdate dataUpdate(final Stmt stmt) {
		return new DataUpdate(stmt);
	}

	static ClockUpdate clockUpdate(final Stmt stmt) {
		return new ClockUpdate(ClockOps.fromStmt(stmt));
	}

	public abstract Stmt toStmt();

	public abstract boolean isDataUpdate();

	public abstract boolean isClockUpdate();

	public abstract DataUpdate asDataUpdate();

	public abstract ClockUpdate asClockUpdate();

	public static final class DataUpdate extends Update {
		private final Stmt stmt;

		private DataUpdate(final Stmt stmt) {
			this.stmt = checkNotNull(stmt);
		}

		@Override
		public Stmt toStmt() {
			return stmt;
		}

		@Override
		public boolean isDataUpdate() {
			return true;
		}

		@Override
		public boolean isClockUpdate() {
			return false;
		}

		@Override
		public DataUpdate asDataUpdate() {
			return this;
		}

		@Override
		public ClockUpdate asClockUpdate() {
			throw new ClassCastException();
		}

		@Override
		public String toString() {
			return stmt.toString();
		}

	}

	public static final class ClockUpdate extends Update {
		private final ClockOp clockOp;

		private ClockUpdate(final ClockOp clockOp) {
			this.clockOp = checkNotNull(clockOp);
		}

		public ClockOp getClockOp() {
			return clockOp;
		}

		@Override
		public Stmt toStmt() {
			return clockOp.toStmt();
		}

		@Override
		public boolean isDataUpdate() {
			return false;
		}

		@Override
		public boolean isClockUpdate() {
			return true;
		}

		@Override
		public DataUpdate asDataUpdate() {
			throw new ClassCastException();
		}

		@Override
		public ClockUpdate asClockUpdate() {
			return this;
		}

		@Override
		public String toString() {
			return clockOp.toString();
		}

	}

}
