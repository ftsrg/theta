/*
 *  Copyright 2025 Budapest University of Technology and Economics
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
package hu.bme.mit.theta.solver.smtlib.solver;

import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.type.LitExpr;
import hu.bme.mit.theta.core.type.Type;
import hu.bme.mit.theta.core.type.enumtype.EnumType;
import hu.bme.mit.theta.solver.Stack;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser;
import hu.bme.mit.theta.solver.smtlib.dsl.gen.SMTLIBv2Parser.Function_defContext;
import hu.bme.mit.theta.solver.smtlib.solver.model.SmtLibModel;
import java.util.*;
import java.util.function.Consumer;

/**
 * EnumTypes need to be handled on SMT solvers too. SmtLib standard contains datatypes, and the
 * behaviour for that is implemented in the DATATYPES strategy. However, most solvers don't support
 * interpolation with datatypes. For this, a workaround is implemented in the SORTS strategy.
 */
public enum SmtLibEnumStrategy {
    DATATYPES {
        @Override
        public void declareDatatypes(
                final Collection<? extends Type> allTypes,
                final Stack<EnumType> typeStack,
                final Consumer<String> issueGeneralCommand) {
            List<Type> types = new ArrayList<>(allTypes);
            types.removeAll(typeStack.toCollection());
            Set<Type> typeSet = new HashSet<>(types);
            for (Type t : typeSet) {
                if (t instanceof EnumType enumType) {
                    typeStack.add(enumType);
                    Collection<String> literals =
                            enumType.getLongValues().stream()
                                    .map(name -> String.format("(%s)", name))
                                    .toList();
                    issueGeneralCommand.accept(
                            String.format(
                                    "(declare-datatypes ((%s 0)) ((%s)))",
                                    enumType.getName(), String.join(" ", literals)));
                }
            }
        }

        @Override
        public LitExpr<EnumType> transformEnumTerm(
                Function_defContext funcDef, EnumType type, SmtLibModel model) {
            final String longName =
                    funcDef.term().qual_identifier().identifier().symbol().getText();
            return type.litFromLongName(longName);
        }
    },

    SORTS {
        @Override
        public void declareDatatypes(
                Collection<? extends Type> allTypes,
                Stack<EnumType> typeStack,
                Consumer<String> issueGeneralCommand) {
            List<Type> types = new ArrayList<>(allTypes);
            types.removeAll(typeStack.toCollection());
            Set<Type> typeSet = new HashSet<>(types);
            for (Type t : typeSet) {
                if (t instanceof EnumType enumType) {
                    typeStack.add(enumType);
                    issueGeneralCommand.accept(
                            String.format("(declare-sort %s 0)", enumType.getName()));
                    enumType.getLongValues()
                            .forEach(
                                    literal ->
                                            issueGeneralCommand.accept(
                                                    String.format(
                                                            "(declare-const %s %s)",
                                                            literal, enumType.getName())));
                    issueGeneralCommand.accept(
                            String.format(
                                    "(assert (distinct %s))",
                                    String.join(" ", enumType.getLongValues())));
                }
            }
        }

        @Override
        public String wrapAssertionExpression(String assertion, Map<ConstDecl<?>, String> consts) {
            boolean needsWrap = false;
            StringBuilder sb = new StringBuilder("(and ").append(assertion);
            for (var constDeclEntry : consts.entrySet()) {
                var constDecl = constDeclEntry.getKey();
                var nameOnSolver = constDeclEntry.getValue();
                if (constDecl.getType() instanceof EnumType enumType) {
                    sb.append(" (or");
                    enumType.getLongValues()
                            .forEach(
                                    val ->
                                            sb.append(
                                                    String.format(
                                                            " (= %s %s)", nameOnSolver, val)));
                    sb.append(")");
                    needsWrap = true;
                }
            }
            sb.append(")");
            return needsWrap ? sb.toString() : assertion;
        }

        @Override
        public LitExpr<EnumType> transformEnumTerm(
                Function_defContext funcDef, EnumType type, SmtLibModel model) {
            final String id = funcDef.term().qual_identifier().identifier().symbol().getText();
            for (var lit : type.getLongValues()) {
                if (model.getTerm(lit).contains(id)) return type.litFromLongName(lit);
            }
            throw new RuntimeException();
        }
    };

    public abstract void declareDatatypes(
            final Collection<? extends Type> allTypes,
            final Stack<EnumType> typeStack,
            final Consumer<String> issueGeneralCommand);

    /**
     * Wraps an expression with additional ones if needed.
     *
     * @param assertion the expression part that was going to be asserted. (e.g. "(= x 1)")
     * @param consts all variables part of the expression
     */
    public String wrapAssertionExpression(
            final String assertion, final Map<ConstDecl<?>, String> consts) {
        return assertion;
    }

    public abstract LitExpr<EnumType> transformEnumTerm(
            final SMTLIBv2Parser.Function_defContext funcDef,
            final EnumType type,
            final SmtLibModel model);

    public static SmtLibEnumStrategy getDefaultStrategy() {
        return SmtLibEnumStrategy.SORTS;
    }
}
