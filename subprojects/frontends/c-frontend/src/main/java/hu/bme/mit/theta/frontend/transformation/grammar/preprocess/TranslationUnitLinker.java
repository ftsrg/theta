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
package hu.bme.mit.theta.frontend.transformation.grammar.preprocess;

import hu.bme.mit.theta.c.frontend.dsl.gen.CLexer;
import hu.bme.mit.theta.c.frontend.dsl.gen.CParser;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.antlr.v4.runtime.CommonToken;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.tree.ParseTree;
import org.antlr.v4.runtime.tree.TerminalNode;

/**
 * What a linker decides about several translation units, read straight off their parse trees.
 *
 * <p>Two things a single-file parse never has to ask. Which definition of an external name counts:
 * several translation units define the same inline function or vtable, and one of them is kept. And
 * which names are not shared at all: {@code static} names of different files are different objects
 * even when spelled alike.
 *
 * <p>The second is solved by renaming, on the tokens, before any frontend visitor runs. Every
 * occurrence of the identifier in that file is renamed, including a struct field or a local that
 * happens to share the spelling; renaming all of them consistently within one file cannot change its
 * meaning, and it spares every later stage from having to know about linkage.
 */
public final class TranslationUnitLinker {

    private TranslationUnitLinker() {}

    /** A function definition: what was declared about it, and in which file. */
    public record FunctionSymbol(
            String name,
            int unit,
            boolean isStatic,
            boolean weak,
            boolean constructor,
            int priority,
            CParser.ExternalFunctionDefinitionContext context) {}

    /** The file-scope names of one translation unit. */
    public record UnitSymbols(
            Set<String> fileScope, Set<String> internal, List<FunctionSymbol> functions) {}

    public static UnitSymbols scan(int unit, CParser.CompilationUnitContext ctx) {
        Set<String> fileScope = new LinkedHashSet<>();
        Set<String> internal = new LinkedHashSet<>();
        List<FunctionSymbol> functions = new ArrayList<>();
        if (ctx.translationUnit() != null) {
            for (CParser.ExternalDeclarationContext external :
                    ctx.translationUnit().externalDeclaration()) {
                if (external instanceof CParser.ExternalFunctionDefinitionContext function) {
                    String name = declaredName(function.functionDefinition().declarator());
                    if (name == null) continue;
                    Set<String> specifiers =
                            tokensOf(function.functionDefinition().declarationSpecifiers());
                    fileScope.add(name);
                    boolean isStatic = specifiers.contains("static");
                    if (isStatic) internal.add(name);
                    functions.add(
                            new FunctionSymbol(
                                    name,
                                    unit,
                                    isStatic,
                                    specifiers.contains("weak"),
                                    specifiers.contains("constructor"),
                                    constructorPriority(
                                            function.functionDefinition().declarationSpecifiers()),
                                    function));
                } else if (external instanceof CParser.GlobalDeclarationContext global) {
                    Set<String> specifiers = tokensOf(global.declaration().declarationSpecifiers());
                    if (specifiers.contains("typedef")
                            || global.declaration().initDeclaratorList() == null) {
                        continue;
                    }
                    for (CParser.InitDeclaratorContext init :
                            global.declaration().initDeclaratorList().initDeclarator()) {
                        String name = declaredName(init.declarator());
                        if (name == null) continue;
                        fileScope.add(name);
                        if (specifiers.contains("static")) internal.add(name);
                    }
                }
            }
        }
        return new UnitSymbols(fileScope, internal, functions);
    }

    /**
     * Gives the internal names that also occur at file scope of another unit a name of their own.
     * Names no other unit uses are left as they are, so that a program split over several files
     * reads like the same program in one.
     *
     * @return per unit, the original name of each renamed symbol and its new name
     */
    public static List<Map<String, String>> renameInternalSymbols(
            List<CParser.CompilationUnitContext> units, List<UnitSymbols> symbols) {
        Map<String, Integer> occurrences = new HashMap<>();
        for (UnitSymbols unit : symbols) {
            unit.fileScope().forEach(name -> occurrences.merge(name, 1, Integer::sum));
        }
        List<Map<String, String>> renames = new ArrayList<>();
        for (int i = 0; i < units.size(); i++) {
            Map<String, String> rename = new LinkedHashMap<>();
            for (String name : symbols.get(i).internal()) {
                if (occurrences.get(name) > 1) rename.put(name, name + "__tu" + i);
            }
            if (!rename.isEmpty()) renameIdentifiers(units.get(i), rename);
            renames.add(rename);
        }
        return renames;
    }

    /** The definition of each external name that the program is linked with: strong over weak. */
    public static Map<String, FunctionSymbol> chooseDefinitions(List<UnitSymbols> symbols) {
        Map<String, FunctionSymbol> chosen = new LinkedHashMap<>();
        for (UnitSymbols unit : symbols) {
            for (FunctionSymbol function : unit.functions()) {
                FunctionSymbol current = chosen.get(function.name());
                if (current == null || (current.weak() && !function.weak())) {
                    chosen.put(function.name(), function);
                }
            }
        }
        return chosen;
    }

    private static void renameIdentifiers(ParseTree tree, Map<String, String> rename) {
        if (tree instanceof TerminalNode terminal) {
            Token token = terminal.getSymbol();
            if (token.getType() == CLexer.Identifier && token instanceof CommonToken common) {
                String renamed = rename.get(common.getText());
                if (renamed != null) common.setText(renamed);
            }
            return;
        }
        for (int i = 0; i < tree.getChildCount(); i++) {
            renameIdentifiers(tree.getChild(i), rename);
        }
    }

    private static String declaredName(CParser.DeclaratorContext declarator) {
        return declaredName(declarator.directDeclarator());
    }

    /** The identifier a declarator declares: the innermost, leftmost part of it. */
    private static String declaredName(CParser.DirectDeclaratorContext direct) {
        for (int i = 0; i < direct.getChildCount(); i++) {
            ParseTree child = direct.getChild(i);
            if (child instanceof CParser.DirectDeclaratorContext inner) return declaredName(inner);
            if (child instanceof CParser.DeclaratorContext inner) return declaredName(inner);
            if (child instanceof TerminalNode terminal
                    && terminal.getSymbol().getType() == CLexer.Identifier) {
                return terminal.getText();
            }
        }
        return null;
    }

    private static Set<String> tokensOf(ParseTree tree) {
        Set<String> tokens = new LinkedHashSet<>();
        collectTokens(tree, tokens);
        return tokens;
    }

    private static void collectTokens(ParseTree tree, Set<String> tokens) {
        if (tree instanceof TerminalNode) {
            tokens.add(tree.getText());
            return;
        }
        for (int i = 0; i < tree.getChildCount(); i++) {
            collectTokens(tree.getChild(i), tokens);
        }
    }

    /** {@code constructor(101)}; without an argument it runs after all that have one. */
    private static int constructorPriority(ParseTree specifiers) {
        List<String> flat = new ArrayList<>();
        flatten(specifiers, flat);
        int at = flat.indexOf("constructor");
        if (at >= 0 && at + 2 < flat.size() && flat.get(at + 1).equals("(")) {
            try {
                return Integer.parseInt(flat.get(at + 2));
            } catch (NumberFormatException e) {
                return Integer.MAX_VALUE;
            }
        }
        return Integer.MAX_VALUE;
    }

    private static void flatten(ParseTree tree, List<String> tokens) {
        if (tree instanceof TerminalNode) {
            tokens.add(tree.getText());
            return;
        }
        for (int i = 0; i < tree.getChildCount(); i++) {
            flatten(tree.getChild(i), tokens);
        }
    }
}
