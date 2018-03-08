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
package hu.bme.mit.theta.xta.tool;

import hu.bme.mit.theta.analysis.algorithm.SearchStrategy;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.lazy.ExplBinItpStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.ExplLuStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.ExplSeqItpStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.ItpStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LazyXtaChecker;
import hu.bme.mit.theta.xta.analysis.lazy.AlgorithmStrategy;
import hu.bme.mit.theta.xta.analysis.lazy.LuStrategy;

public final class XtaCheckerBuilder {

	public enum Algorithm {

		SEQITP {
			@Override
			public AlgorithmStrategy<?> create(final XtaSystem system) {
				return ItpStrategy.createForward(system);
			}
		},

		BINITP {
			@Override
			public AlgorithmStrategy<?> create(final XtaSystem system) {
				return ItpStrategy.createBackward(system);
			}
		},

		LU {
			@Override
			public AlgorithmStrategy<?> create(final XtaSystem system) {
				return LuStrategy.create(system);
			}
		},

		EXPLSEQITP {
			@Override
			public AlgorithmStrategy<?> create(final XtaSystem system) {
				return ExplSeqItpStrategy.create(system);
			}
		},

		EXPLBINITP {
			@Override
			public AlgorithmStrategy<?> create(final XtaSystem system) {
				return ExplBinItpStrategy.create(system);
			}
		},

		EXPLLU {
			@Override
			public AlgorithmStrategy<?> create(final XtaSystem system) {
				return ExplLuStrategy.create(system);
			}
		};

		public abstract AlgorithmStrategy<?> create(final XtaSystem system);
	}

	private XtaCheckerBuilder() {
	}

	public static LazyXtaChecker<?> build(final Algorithm algorithm, final SearchStrategy searchStrategy,
			final XtaSystem xta) {
		final AlgorithmStrategy<?> algorithmStrategy = algorithm.create(xta);

		final LazyXtaChecker<?> checker = LazyXtaChecker.create(xta, algorithmStrategy, searchStrategy);
		return checker;
	}
}
