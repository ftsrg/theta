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

public abstract class SearchStrategy {

	private SearchStrategy() {
	}

	public abstract <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist();

	public static SearchStrategy breadthFirst() {
		return BreadthFirst.INSTANCE;
	}

	public static SearchStrategy depthFirst() {
		return DepthFirst.INSTANCE;
	}

	public static SearchStrategy random() {
		return Random.INSTANCE;
	}

	public static final class BreadthFirst extends SearchStrategy {
		private static final BreadthFirst INSTANCE = new BreadthFirst();

		private BreadthFirst() {
		}

		@Override
		public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
			return FifoWaitlist.create();
		}
	}

	public static final class DepthFirst extends SearchStrategy {
		private static final DepthFirst INSTANCE = new DepthFirst();

		private DepthFirst() {
		}

		@Override
		public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
			return LifoWaitlist.create();
		}
	}

	public static final class Random extends SearchStrategy {
		private static final Random INSTANCE = new Random();

		private Random() {
		}

		@Override
		public <S extends State, A extends Action> Waitlist<ArgNode<S, A>> createWaitlist() {
			return RandomWaitlist.create();
		}
	}

}
