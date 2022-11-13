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

package hu.bme.mit.theta.xcfa.model;

import hu.bme.mit.theta.core.stmt.StmtVisitor;
import hu.bme.mit.theta.core.type.Type;

public interface XcfaLabelVisitor<P, R> extends StmtVisitor<P, R> {
	R visit(XcfaLabel.AtomicBeginXcfaLabel label, P param);

	R visit(XcfaLabel.AtomicEndXcfaLabel label, P param);

	R visit(XcfaLabel.ProcedureCallXcfaLabel label, P param);

	R visit(XcfaLabel.StartThreadXcfaLabel label, P param);

	R visit(XcfaLabel.JoinThreadXcfaLabel label, P param);

	<T extends Type> R visit(XcfaLabel.LoadXcfaLabel<T> label, P param);

	<T extends Type> R visit(XcfaLabel.StoreXcfaLabel<T> label, P param);

	R visit(XcfaLabel.FenceXcfaLabel label, P param);

	R visit(XcfaLabel.StmtXcfaLabel label, P param);

	R visit(XcfaLabel.SequenceLabel sequenceLabel, P param);

	R visit(XcfaLabel.NondetLabel nondetLabel, P param);

}
