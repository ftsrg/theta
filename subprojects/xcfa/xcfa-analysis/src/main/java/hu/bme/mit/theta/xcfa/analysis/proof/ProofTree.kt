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
package hu.bme.mit.theta.xcfa.analysis.proof

import hu.bme.mit.theta.analysis.algorithm.arg.ArgNode

/**
 * The nodes of a CEGAR checker's last reachability tree (ARG), kept only when the checker is asked
 * to (DSS's `--dss-tree-postcondition` and `--dss-violation-conditions GRAPH_PATHS`). On a safe
 * result it is the complete tree the [LocationInvariants] come from; on an unsafe one, the tree the
 * counterexample was found in, with its other target nodes. The states are `XcfaState`s and the
 * actions `XcfaAction`s, over the checker's own (process-renamed) variables.
 */
class ProofTree(val nodes: List<ArgNode<*, *>>)
