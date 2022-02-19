/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.analysis.expr;

import java.util.Map;

public interface MultiExprState<P, S extends ExprState> extends ExprState {
	MultiExprState<P, S> add(P p, S s);

	MultiExprState<P, S> remove(P p);

	MultiExprState<P, S> update(P p, S s);

	Map<P, S> getStates();
}
