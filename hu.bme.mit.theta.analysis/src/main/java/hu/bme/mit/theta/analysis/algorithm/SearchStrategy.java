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
package hu.bme.mit.theta.analysis.algorithm;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.waitlist.FifoWaitlist;
import hu.bme.mit.theta.analysis.waitlist.LifoWaitlist;
import hu.bme.mit.theta.analysis.waitlist.RandomWaitlist;
import hu.bme.mit.theta.analysis.waitlist.Waitlist;

public enum SearchStrategy {

	BFS {

		@Override
		public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
			return FifoWaitlist.create();
		}

	},

	DFS {

		@Override
		public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
			return LifoWaitlist.create();
		}

	},

	RANDOM {

		@Override
		public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
			return RandomWaitlist.create();
		}

	};

	public abstract <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist();

}
