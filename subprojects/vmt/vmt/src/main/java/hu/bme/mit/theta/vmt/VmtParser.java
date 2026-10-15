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
package hu.bme.mit.theta.vmt;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.Formula;
import org.sosy_lab.java_smt.api.FormulaManager;
import org.sosy_lab.java_smt.api.FormulaType;

/**
 * Reads a VMT-LIB file into a {@link VmtModel}. Only the top-level command structure and the {@code
 * !} annotations are read here; every term is parsed by the solver through {@link
 * FormulaManager#parse(String)}, so any SMT-LIB term the solver accepts can be used.
 *
 * <p>Annotations are removed before the solver sees the text, as some solvers reject unknown
 * attributes. Each annotated definition body is parsed on its own, after all declarations and
 * definitions of the file.
 */
public final class VmtParser {

    private final FormulaManager fmgr;

    private VmtParser(FormulaManager fmgr) {
        this.fmgr = fmgr;
    }

    public static VmtModel parse(Path file, FormulaManager fmgr) throws IOException {
        return parse(Files.readString(file), fmgr);
    }

    public static VmtModel parse(String text, FormulaManager fmgr) {
        return new VmtParser(fmgr).parse(text);
    }

    private record NextLink(String current, String next) {}

    private record AnnotatedProperty(VmtProperty.Kind kind, int index, String name, SExpr body) {}

    private VmtModel parse(String text) {
        final StringBuilder prefix = new StringBuilder();
        final Map<String, SExpr> constSorts = new LinkedHashMap<>();
        final List<NextLink> nextLinks = new ArrayList<>();
        final List<SExpr> initBodies = new ArrayList<>();
        final List<SExpr> transBodies = new ArrayList<>();
        final List<AnnotatedProperty> propertyBodies = new ArrayList<>();

        for (SExpr command : SExprParser.parseAll(text)) {
            if (!(command instanceof SExpr.SList list)
                    || list.size() == 0
                    || !(list.get(0) instanceof SExpr.Atom head)) {
                throw new VmtParseException("Expected a command, got " + command);
            }
            switch (head.text()) {
                case "set-logic", "set-info", "set-option", "check-sat", "exit", "get-model" -> {}
                case "declare-sort", "define-sort" -> prefix.append(list).append('\n');
                case "declare-const" -> {
                    expectSize(list, 3);
                    constSorts.put(symbol(list.get(1)), list.get(2));
                    prefix.append(list).append('\n');
                }
                case "declare-fun" -> {
                    expectSize(list, 4);
                    if (list.get(2) instanceof SExpr.SList args && args.size() == 0) {
                        constSorts.put(symbol(list.get(1)), list.get(3));
                    }
                    prefix.append(list).append('\n');
                }
                case "define-fun" -> {
                    expectSize(list, 5);
                    final String name = symbol(list.get(1));
                    final SExpr body = list.get(4);
                    final SExpr stripped = stripAnnotations(body);
                    prefix.append(
                                    new SExpr.SList(
                                            List.of(
                                                    list.get(0),
                                                    list.get(1),
                                                    list.get(2),
                                                    list.get(3),
                                                    stripped)))
                            .append('\n');
                    final boolean nullary =
                            list.get(2) instanceof SExpr.SList args && args.size() == 0;
                    if (nullary
                            && body instanceof SExpr.SList annotated
                            && annotated.startsWith("!")) {
                        readAnnotations(
                                name,
                                annotated,
                                stripped,
                                nextLinks,
                                initBodies,
                                transBodies,
                                propertyBodies);
                    }
                }
                case "assert" -> {
                    // VMT files conventionally end with (assert true); anything else has no
                    // transition-system meaning
                    if (list.size() != 2 || !isTrue(list.get(1))) {
                        throw new VmtParseException(
                                "Plain assert commands are not part of VMT: " + list);
                    }
                }
                default -> throw new VmtParseException("Unsupported command: " + head.text());
            }
        }

        // a next-state symbol may be left undeclared; it takes the sort of its state variable,
        // and is declared up front, as definitions may use it
        final StringBuilder implicit = new StringBuilder();
        for (NextLink link : nextLinks) {
            final SExpr sort = constSorts.get(link.current());
            if (sort != null && !constSorts.containsKey(link.next())) {
                constSorts.put(link.next(), sort);
                implicit.append("(declare-fun |")
                        .append(link.next())
                        .append("| () ")
                        .append(sort)
                        .append(")\n");
            }
        }

        final String declarations = implicit + prefix.toString();
        final BooleanFormulaManager bmgr = fmgr.getBooleanFormulaManager();

        final List<VmtStateVar> stateVars = new ArrayList<>();
        final Set<String> stateSymbols = new LinkedHashSet<>();
        for (NextLink link : nextLinks) {
            final SExpr sort = constSorts.get(link.current());
            if (sort == null) {
                throw new VmtParseException("Undeclared state variable: " + link.current());
            }
            if (!sort.equals(constSorts.get(link.next()))) {
                throw new VmtParseException(
                        "Next-state variable "
                                + link.next()
                                + " must be declared with sort "
                                + sort);
            }
            final FormulaType<?> type = toFormulaType(sort);
            if (type == null) {
                throw new VmtParseException(
                        "Unsupported sort " + sort + " of state variable " + link.current());
            }
            stateVars.add(
                    new VmtStateVar(
                            link.current(),
                            fmgr.makeVariable(type, link.current()),
                            link.next(),
                            fmgr.makeVariable(type, link.next()),
                            type));
            stateSymbols.add(link.current());
            stateSymbols.add(link.next());
        }

        final List<Formula> inputVars = new ArrayList<>();
        for (Map.Entry<String, SExpr> entry : constSorts.entrySet()) {
            if (stateSymbols.contains(entry.getKey())) continue;
            final FormulaType<?> type = toFormulaType(entry.getValue());
            if (type != null) inputVars.add(fmgr.makeVariable(type, entry.getKey()));
        }

        final BooleanFormula init = parseConjunction(declarations, initBodies, bmgr);
        final BooleanFormula trans = parseConjunction(declarations, transBodies, bmgr);
        final List<VmtProperty> properties = new ArrayList<>();
        for (AnnotatedProperty p : propertyBodies) {
            properties.add(
                    new VmtProperty(
                            p.kind(), p.index(), p.name(), parseTerm(declarations, p.body())));
        }
        return new VmtModel(fmgr, stateVars, inputVars, init, trans, properties);
    }

    private void readAnnotations(
            String name,
            SExpr.SList annotated,
            SExpr stripped,
            List<NextLink> nextLinks,
            List<SExpr> initBodies,
            List<SExpr> transBodies,
            List<AnnotatedProperty> propertyBodies) {
        if (annotated.size() % 2 != 0) {
            throw new VmtParseException("Malformed annotation in " + name + ": " + annotated);
        }
        for (int i = 2; i < annotated.size(); i += 2) {
            final String key = annotated.get(i).toString();
            final SExpr value = annotated.get(i + 1);
            switch (key) {
                case ":next" -> {
                    if (!(stripped instanceof SExpr.Atom current)) {
                        throw new VmtParseException(
                                ":next must annotate a variable, got " + stripped);
                    }
                    nextLinks.add(new NextLink(current.symbolName(), symbol(value)));
                }
                case ":init" -> {
                    if (isTrue(value)) initBodies.add(stripped);
                }
                case ":trans" -> {
                    if (isTrue(value)) transBodies.add(stripped);
                }
                case ":invar-property" ->
                        propertyBodies.add(
                                new AnnotatedProperty(
                                        VmtProperty.Kind.INVARIANT, index(value), name, stripped));
                case ":live-property" ->
                        propertyBodies.add(
                                new AnnotatedProperty(
                                        VmtProperty.Kind.LIVENESS, index(value), name, stripped));
                default -> {
                    // other attributes (e.g. :named) carry no transition-system meaning
                }
            }
        }
    }

    private BooleanFormula parseConjunction(
            String declarations, List<SExpr> bodies, BooleanFormulaManager bmgr) {
        final List<BooleanFormula> parts = new ArrayList<>();
        for (SExpr body : bodies) parts.add(parseTerm(declarations, body));
        return bmgr.and(parts);
    }

    private BooleanFormula parseTerm(String declarations, SExpr body) {
        try {
            return fmgr.parse(declarations + "(assert " + body + ")\n");
        } catch (IllegalArgumentException e) {
            throw new VmtParseException("The solver could not parse " + body, e);
        }
    }

    private static SExpr stripAnnotations(SExpr expr) {
        if (expr instanceof SExpr.SList list) {
            if (list.startsWith("!") && list.size() >= 2) return stripAnnotations(list.get(1));
            return new SExpr.SList(list.elems().stream().map(VmtParser::stripAnnotations).toList());
        }
        return expr;
    }

    private static FormulaType<?> toFormulaType(SExpr sort) {
        if (sort instanceof SExpr.Atom atom) {
            return switch (atom.text()) {
                case "Bool" -> FormulaType.BooleanType;
                case "Int" -> FormulaType.IntegerType;
                case "Real" -> FormulaType.RationalType;
                default -> null;
            };
        }
        final SExpr.SList list = (SExpr.SList) sort;
        if (list.size() == 3 && list.startsWith("_") && list.get(1).toString().equals("BitVec")) {
            return FormulaType.getBitvectorTypeWithSize(Integer.parseInt(list.get(2).toString()));
        }
        return null;
    }

    private static String symbol(SExpr expr) {
        if (expr instanceof SExpr.Atom atom) return atom.symbolName();
        throw new VmtParseException("Expected a symbol, got " + expr);
    }

    private static boolean isTrue(SExpr value) {
        return value instanceof SExpr.Atom a && a.isSymbol("true");
    }

    private static int index(SExpr value) {
        try {
            return Integer.parseInt(value.toString());
        } catch (NumberFormatException e) {
            throw new VmtParseException("Expected a property index, got " + value);
        }
    }

    private static void expectSize(SExpr.SList list, int size) {
        if (list.size() != size) throw new VmtParseException("Malformed command: " + list);
    }
}
