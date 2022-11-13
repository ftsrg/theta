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

package hu.bme.mit.theta.frontend.transformation.model.statements;

import hu.bme.mit.theta.core.type.Expr;

/**
 * Every Program, Function and Statement is a subclass of this base class.
 * Any CStatement might have an id associated with it, in case there was a label in the source code. This also provides
 * an XcfaLocation, which can be used when jumping to this named location via a _goto_ instruction
 */
public abstract class CStatement {
	private String id;
	protected static int counter = 0;
	protected CStatement preStatements;
	protected CStatement postStatements;

	public String getId() {
		return id;
	}

	public void setId(String id) {
		this.id = id;
	}

	/**
	 * Returns the expression associated with a CStatement, which by default throws an exception, as not all subtypes
	 * will return one. For example, the C language statement `int a = (b = 0, 2)` will create a CCompound statement as
	 * the right-hand side of the assignment, whose associated expression will be 2, but the assignment to b has to come
	 * beforehand.
	 *
	 * @return The expression associated with the statement.
	 */
	public Expr<?> getExpression() {
		throw new RuntimeException("Cannot get expression!");
	}

	public CStatement getPostStatements() {
		return postStatements;
	}

	public void setPostStatements(CStatement postStatements) {
		throw new UnsupportedOperationException("Only CCompounds shall currently have pre- and post statements!");
	}

	public CStatement getPreStatements() {
		return preStatements;
	}

	public void setPreStatements(CStatement preStatements) {
		throw new UnsupportedOperationException("Only CCompounds shall currently have pre- and post statements!");
	}

	public abstract <P, R> R accept(CStatementVisitor<P, R> visitor, P param);
}
