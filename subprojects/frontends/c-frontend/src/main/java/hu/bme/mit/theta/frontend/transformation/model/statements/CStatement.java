/*
 *  Copyright 2023 Budapest University of Technology and Economics
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
import hu.bme.mit.theta.frontend.ParseContext;

/**
 * Every Program, Function and Statement is a subclass of this base class.
 * Any CStatement might have an id associated with it, in case there was a label in the source code. This also provides
 * an XcfaLocation, which can be used when jumping to this named location via a _goto_ instruction
 */
public abstract class CStatement {
    protected final ParseContext parseContext;
    private String id;
    protected static int counter = 0;
    protected CStatement preStatements;
    protected CStatement postStatements;

    private int lineNumberStart = -1;
    private int colNumberStart = -1;
    private int lineNumberStop = -1;
    private int colNumberStop = -1;
    private int offsetStart = -1;
    private int offsetEnd = -1;
    private String sourceText = "";

    protected CStatement(ParseContext parseContext) {
        this.parseContext = parseContext;
    }

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

    public int getLineNumberStart() {
        return lineNumberStart;
    }

    public void setLineNumberStart(int lineNumberStart) {
        this.lineNumberStart = lineNumberStart;
    }

    public int getColNumberStart() {
        return colNumberStart;
    }

    public void setColNumberStart(int colNumberStart) {
        this.colNumberStart = colNumberStart;
    }

    public int getLineNumberStop() {
        return lineNumberStop;
    }

    public void setLineNumberStop(int lineNumberStop) {
        this.lineNumberStop = lineNumberStop;
    }

    public int getColNumberStop() {
        return colNumberStop;
    }

    public void setColNumberStop(int colNumberStop) {
        this.colNumberStop = colNumberStop;
    }

    public int getOffsetStart() {
        return offsetStart;
    }

    public void setOffsetStart(int offsetStart) {
        this.offsetStart = offsetStart;
    }

    public int getOffsetEnd() {
        return offsetEnd;
    }

    public void setOffsetEnd(int offsetEnd) {
        this.offsetEnd = offsetEnd;
    }

    public String getSourceText() {
        return sourceText;
    }

    public void setSourceText(String sourceText) {
        this.sourceText = sourceText;
    }
}
