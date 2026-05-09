/*
 *  Copyright 2026 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.Trace;
import hu.bme.mit.theta.analysis.algorithm.arg.ARG;
import hu.bme.mit.theta.analysis.algorithm.cegar.AbstractorResult;

public class LazyAbstractorResult extends AbstractorResult {

  private final LazyStatistics stats;
  private ARG<? extends State, ? extends Action> proof;
  private Trace<? extends State, ? extends Action> cex;

  private LazyAbstractorResult(final boolean safe,
                               final ARG<? extends State, ? extends Action> proof,
                               final Trace<? extends State, ? extends Action> cex,
                               final LazyStatistics stats) {
    super(safe);
    this.proof = proof;
    this.cex = cex;
    this.stats = stats;
  }

  public static <S extends State, A extends Action> LazyAbstractorResult safe(
      final ARG<S, A> proof, final LazyStatistics stats
  ) {
    return new LazyAbstractorResult(true, proof, null, stats);
  }

  public static LazyAbstractorResult unsafe(
      final Trace<? extends State, ? extends Action> cex,
      final ARG<? extends State, ? extends Action> proof,
      final LazyStatistics stats
  ) {
    return new LazyAbstractorResult(false, proof, cex, stats);
  }

  public ARG<? extends State, ? extends Action> getProof() {
    return proof;
  }

  public Trace<? extends State, ? extends Action> getCex() {
    if (isUnsafe()) {
      return cex;
    } else {
      throw new IllegalStateException();
    }
  }

  public LazyStatistics getStats() {
    return stats;
  }
}
