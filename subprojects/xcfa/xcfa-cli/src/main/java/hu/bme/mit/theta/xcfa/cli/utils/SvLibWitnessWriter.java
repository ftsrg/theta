package hu.bme.mit.theta.xcfa.cli.utils;

import static hu.bme.mit.theta.core.type.booltype.BoolExprs.Or;
import static hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable.encodeSymbol;

import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.core.decl.ConstDecl;
import hu.bme.mit.theta.core.decl.Decl;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;
import hu.bme.mit.theta.core.utils.ExprUtils;
import hu.bme.mit.theta.frontend.ParseContext;
import hu.bme.mit.theta.frontend.svlib.SvLibMetadata;
import hu.bme.mit.theta.frontend.transformation.ArchitectureConfig;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSymbolTable;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibTransformationManager;
import hu.bme.mit.theta.xcfa.XcfaProperty;
import hu.bme.mit.theta.xcfa.analysis.proof.LocationInvariants;
import hu.bme.mit.theta.xcfa.model.XcfaLocation;
import java.io.File;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.stream.Collectors;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

public final class SvLibWitnessWriter implements XcfaWitnessWriter {

    @Override
    public @NotNull String getExtension() {
        return "svlib";
    }

    @Override
    public void writeWitness(
            @NotNull final SafetyResult<?, ?> safetyResult,
            @NotNull final File inputFile,
            @NotNull final XcfaProperty property,
            @NotNull final SolverFactory cexSolverFactory,
            @NotNull final ParseContext parseContext,
            @NotNull final File witnessfile,
            @NotNull final String ltlSpecification,
            @Nullable final ArchitectureConfig.ArchitectureType architecture,
            @NotNull final Logger logger) {
        if (safetyResult.isSafe() && safetyResult.getProof() instanceof LocationInvariants proof) {
            writeString(witnessfile, toSvLibCorrectnessWitness(proof));
        }
    }

    @Override
    public void writeTrivialCorrectnessWitness(
            @NotNull final SafetyResult<?, ?> safetyResult,
            @NotNull final File inputFile,
            @NotNull final XcfaProperty property,
            @NotNull final ParseContext parseContext,
            @NotNull final File witnessfile,
            @NotNull final String ltlSpecification,
            @Nullable final ArchitectureConfig.ArchitectureType architecture) {
        // No SV-LIB annotation can be emitted without location invariants and tagged locations.
    }

    @Override
    public @NotNull String generateEmptyViolationWitness(
            @NotNull final File inputFile,
            @NotNull final String ltlSpecification,
            @Nullable final ArchitectureConfig.ArchitectureType architecture) {
        throw new UnsupportedOperationException("SV-LIB violation witnesses are not supported");
    }

    private static String toSvLibCorrectnessWitness(final LocationInvariants proof) {
        final Map<String, Expr<BoolType>> invariantsByTag = locationInvariantsByTag(proof);
        if (invariantsByTag.isEmpty()) {
            return emptyWitness();
        }

        final SvLibTermTransformer transformer =
                new SvLibTermTransformer(invariantsByTag.values());
        final String annotations =
                new TreeMap<>(invariantsByTag).entrySet().stream()
                        .map(
                                entry ->
                                        "(annotate-tag\n"
                                                + "    "
                                                + encodeSymbol(entry.getKey())
                                                + "\n"
                                                + "    :invariant\n"
                                                + indent(transformer.toTerm(entry.getValue()), 8)
                                                + ")")
                        .collect(Collectors.joining("\n\n"));

        return "(" + annotations + ")\n";
    }

    private static Map<String, Expr<BoolType>> locationInvariantsByTag(
            final LocationInvariants proof) {
        final Map<String, List<Expr<BoolType>>> invariants = new LinkedHashMap<>();

        for (final Map.Entry<XcfaLocation, Collection<ExprState>> entry :
                proof.getPartitions().entrySet()) {
            final String tag = svLibTag(entry.getKey());
            if (tag == null || entry.getValue().isEmpty()) {
                continue;
            }
            invariants.computeIfAbsent(tag, unused -> new ArrayList<>())
                    .add(ExprUtils.simplify(Or(entry.getValue().stream()
                            .map(ExprState::getInvariant)
                            .collect(Collectors.toList()))));
        }

        return simplifyByTag(invariants);
    }

    private static Map<String, Expr<BoolType>> simplifyByTag(
            final Map<String, List<Expr<BoolType>>> invariants) {
        return invariants.entrySet().stream()
                .collect(
                        Collectors.toMap(
                                Map.Entry::getKey,
                                entry -> ExprUtils.simplify(Or(entry.getValue())),
                                (left, right) -> left,
                                LinkedHashMap::new));
    }

    private static String svLibTag(@Nullable final XcfaLocation location) {
        if (location != null
                && location.getMetadata() instanceof SvLibMetadata metadata
                && metadata.isTag()) {
            return metadata.getTag();
        }
        return null;
    }

    private static String indent(final String text, final int spaces) {
        final String prefix = " ".repeat(spaces);
        return text.lines().map(line -> prefix + line).collect(Collectors.joining("\n")) + "\n";
    }

    private static String emptyWitness() {
        return "()\n";
    }

    private static void writeString(final File file, final String content) {
        try {
            Files.writeString(file.toPath(), content);
        } catch (final IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    private static final class SvLibTermTransformer {
        private final GenericSmtLibSymbolTable symbolTable = new GenericSmtLibSymbolTable();
        private final GenericSmtLibTransformationManager transformationManager =
                new GenericSmtLibTransformationManager(symbolTable);
        private final Map<VarDecl<?>, ConstDecl<?>> variableConstants = new LinkedHashMap<>();

        private SvLibTermTransformer(final Collection<Expr<BoolType>> expressions) {
            expressions.forEach(this::registerVariables);
        }

        private String toTerm(final Expr<BoolType> expr) {
            registerVariables(expr);
            final Expr<BoolType> printableExpr = replaceVariablesWithConstants(expr);
            registerConstants(printableExpr);
            return transformationManager.toTerm(printableExpr);
        }

        private void registerVariables(final Expr<?> expr) {
            for (final VarDecl<?> varDecl : ExprUtils.getVars(expr)) {
                variableConstants.computeIfAbsent(
                        varDecl, var -> Decls.Const(var.getName(), var.getType()));
            }
        }

        @SuppressWarnings("unchecked")
        private Expr<BoolType> replaceVariablesWithConstants(final Expr<BoolType> expr) {
            final Map<Decl<?>, Decl<?>> decls = new LinkedHashMap<>(variableConstants);
            return (Expr<BoolType>) ExprUtils.changeDecls(expr, decls);
        }

        private void registerConstants(final Expr<?> expr) {
            final List<ConstDecl<?>> constants = new ArrayList<>();
            ExprUtils.collectConstants(expr, constants);
            for (final ConstDecl<?> decl : constants) {
                if (!symbolTable.definesConst(decl)) {
                    symbolTable.put(decl, encodeSymbol(decl.getName()), "");
                }
            }
        }
    }
}
