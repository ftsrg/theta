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
package hu.bme.mit.theta.formalism.cfa.analysis.impact;

import static com.google.common.base.Preconditions.checkNotNull;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;

public interface ImpactRefiner<S extends State, A extends Action> {

	RefinementResult<S, A> refine(final Trace<S, A> cex);

	abstract class RefinementResult<S extends State, A extends Action> {

		private RefinementResult() {
		}

		public static <S extends State, A extends Action> Succesful<S, A> succesful(final Trace<S, A> trace) {
			return new Succesful<>(trace);
		}

		public static <S extends State, A extends Action> Unsuccesful<S, A> unsuccesful() {
			return new Unsuccesful<>();
		}

		public abstract boolean isSuccesful();

		public abstract boolean isUnsuccesful();

		public abstract Succesful<S, A> asSuccesful();

		public abstract Unsuccesful<S, A> asUnsuccesful();
	}

	final class Succesful<S extends State, A extends Action> extends RefinementResult<S, A> {
		private final Trace<S, A> trace;

		private Succesful(final Trace<S, A> trace) {
			this.trace = checkNotNull(trace);
		}

		public Trace<S, A> getTrace() {
			return trace;
		}

		@Override
		public boolean isSuccesful() {
			return true;
		}

		@Override
		public boolean isUnsuccesful() {
			return false;
		}

		@Override
		public Succesful<S, A> asSuccesful() {
			return this;
		}

		@Override
		public Unsuccesful<S, A> asUnsuccesful() {
			throw new ClassCastException();
		}
	}

	final class Unsuccesful<S extends State, A extends Action> extends RefinementResult<S, A> {

		private Unsuccesful() {
		}

		@Override
		public boolean isSuccesful() {
			return false;
		}

		@Override
		public boolean isUnsuccesful() {
			return true;
		}

		@Override
		public Succesful<S, A> asSuccesful() {
			throw new ClassCastException();
		}

		@Override
		public Unsuccesful<S, A> asUnsuccesful() {
			return this;
		}
	}

}
