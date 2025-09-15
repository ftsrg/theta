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
package hu.bme.mit.theta.solver.smtlib;

import static com.google.common.base.Preconditions.*;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.*;
import hu.bme.mit.theta.solver.smtlib.impl.bitwuzla.BitwuzlaSmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.boolector.BoolectorSmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.cvc4.CVC4SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.cvc5.CVC5SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.eldarica.EldaricaSmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.generic.GenericSmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.golem.GolemSmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.mathsat.MathSATSmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.princess.PrincessSmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.smtinterpol.SMTInterpolSmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.impl.z3.Z3SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.solver.installer.SmtLibSolverInstallerException;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public final class SmtLibSolverManager extends SolverManager {

    public static final Path HOME = Path.of(System.getProperty("user.home"), ".theta");

    private static final Map<String, Class<? extends SmtLibSolverInstaller>> installerDeclarations =
            new HashMap<>();
    private static Tuple2<String, Class<? extends GenericSmtLibSolverInstaller>>
            genericInstallerDeclaration;

    static {
        registerInstaller("z3", Z3SmtLibSolverInstaller.class);
        registerInstaller("cvc4", CVC4SmtLibSolverInstaller.class);
        registerInstaller("cvc5", CVC5SmtLibSolverInstaller.class);
        registerInstaller("mathsat", MathSATSmtLibSolverInstaller.class);
        registerInstaller("boolector", BoolectorSmtLibSolverInstaller.class);
        registerInstaller("bitwuzla", BitwuzlaSmtLibSolverInstaller.class);
        registerInstaller("smtinterpol", SMTInterpolSmtLibSolverInstaller.class);
        registerInstaller("princess", PrincessSmtLibSolverInstaller.class);
        registerInstaller("eldarica", EldaricaSmtLibSolverInstaller.class);
        registerInstaller("golem", GolemSmtLibSolverInstaller.class);
        registerGenericInstaller("generic", GenericSmtLibSolverInstaller.class);
    }

    private final Path home;
    private final Map<String, SmtLibSolverInstaller> installers;
    private final Tuple2<String, GenericSmtLibSolverInstaller> genericInstaller;
    private final Set<SolverBase> instantiatedSolvers;
    private boolean closed = false;

    private SmtLibSolverManager(final Path home, final Logger logger) {
        checkNotNull(home);
        checkArgument(Files.exists(home), "Home directory does not exist");

        this.home = home;

        try {
            this.genericInstaller =
                    Tuple2.of(
                            genericInstallerDeclaration.get1(),
                            genericInstallerDeclaration
                                    .get2()
                                    .getDeclaredConstructor(Logger.class)
                                    .newInstance(logger));

            this.installers =
                    Stream.concat(
                                    Stream.of(this.genericInstaller),
                                    installerDeclarations.entrySet().stream()
                                            .map(
                                                    p -> {
                                                        try {
                                                            return Tuple2.of(
                                                                    p.getKey(),
                                                                    p.getValue()
                                                                            .getDeclaredConstructor(
                                                                                    Logger.class)
                                                                            .newInstance(logger));
                                                        } catch (InstantiationException
                                                                | IllegalAccessException
                                                                | InvocationTargetException
                                                                | NoSuchMethodException e) {
                                                            throw new RuntimeException(e);
                                                        }
                                                    }))
                            .collect(Collectors.toUnmodifiableMap(Tuple2::get1, Tuple2::get2));
        } catch (InstantiationException
                | InvocationTargetException
                | NoSuchMethodException
                | IllegalAccessException e) {
            throw new RuntimeException(e);
        }

        this.instantiatedSolvers = new HashSet<>();
    }

    public static <T extends SmtLibSolverInstaller> void registerInstaller(
            final String name, final Class<T> decl) {
        installerDeclarations.put(name, decl);
    }

    public static <T extends GenericSmtLibSolverInstaller> void registerGenericInstaller(
            final String name, final Class<T> decl) {
        checkState(genericInstallerDeclaration == null);
        genericInstallerDeclaration = Tuple2.of(name, decl);
    }

    public static String getSolverName(final String name) {
        final var solverName = decodeSolverName(name, 0);
        if (solverName != null) {
            return solverName;
        } else {
            throw new IllegalArgumentException("Invalid version string: " + name);
        }
    }

    public static String getSolverVersion(final String name) {
        final var solverVersion = decodeSolverName(name, 1);
        if (solverVersion != null) {
            return solverVersion;
        } else {
            throw new IllegalArgumentException("Invalid version string: " + name);
        }
    }

    private static String decodeSolverName(final String name, final int part) {
        final var versionArr = name.split(":");

        if (versionArr.length != 2) {
            return null;
        }

        return versionArr[part];
    }

    public static SmtLibSolverManager create(final Path home, final Logger logger)
            throws IOException {
        return new SmtLibSolverManager(createIfNotExists(home), logger);
    }

    private static Path createIfNotExists(final Path path) throws IOException {
        if (!Files.exists(path)) {
            Files.createDirectory(path);
        }
        return path;
    }

    public String getGenericInstallerName() {
        return genericInstaller.get1();
    }

    @Override
    public boolean managesSolver(final String name) {
        final var solverName = decodeSolverName(name, 0);
        return solverName != null && installers.containsKey(solverName);
    }

    public void install(
            final String solver,
            final String version,
            final String name,
            final Path solverPath,
            final boolean installUnsupported)
            throws SmtLibSolverInstallerException {
        checkArgument(!solver.equals(genericInstaller.get1()));

        if (!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        } else if (!getSupportedVersions(solver).contains(getVersionString(solver, version, false))
                && !installUnsupported) {
            throw new SmtLibSolverInstallerException(
                    "Installing unsupported solvers is not enabled");
        }

        final var installDir = home.resolve(solver);
        try {
            if (!Files.exists(installDir)) {
                Files.createDirectory(installDir);
            }
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        if (solverPath != null) {
            installers
                    .get(solver)
                    .install(
                            installDir,
                            getVersionString(solver, version, false),
                            getVersionString(solver, name, false),
                            solverPath);
        } else {
            installers
                    .get(solver)
                    .install(
                            installDir,
                            getVersionString(solver, version, false),
                            getVersionString(solver, name, false));
        }
    }

    public void installGeneric(final String version, final Path solverPath, final String[] args)
            throws SmtLibSolverInstallerException {
        final var installDir = home.resolve(genericInstaller.get1());
        try {
            if (!Files.exists(installDir)) {
                Files.createDirectory(installDir);
            }
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }
        genericInstaller.get2().install(installDir, version, solverPath, args);
    }

    public void uninstall(final String solver, final String version)
            throws SmtLibSolverInstallerException {
        if (!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        installers
                .get(solver)
                .uninstall(home.resolve(solver), getVersionString(solver, version, true));
    }

    public void rename(final String solver, final String version, final String name)
            throws SmtLibSolverInstallerException {
        if (!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        installers
                .get(solver)
                .rename(home.resolve(solver), getVersionString(solver, version, true), name);
    }

    public String getInfo(final String solver, final String version)
            throws SmtLibSolverInstallerException {
        if (!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return installers
                .get(solver)
                .getInfo(home.resolve(solver), getVersionString(solver, version, true));
    }

    public Path getArgsFile(final String solver, final String version)
            throws SmtLibSolverInstallerException {
        if (!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return installers
                .get(solver)
                .getArgsFile(home.resolve(solver), getVersionString(solver, version, true));
    }

    @Override
    public SolverFactory getSolverFactory(final String name) throws SmtLibSolverInstallerException {
        checkArgument(managesSolver(name));
        return getSolverFactory(getSolverName(name), getSolverVersion(name));
    }

    public SolverFactory getSolverFactory(final String solver, final String version)
            throws SmtLibSolverInstallerException {
        if (!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return new ManagedFactory(
                installers
                        .get(solver)
                        .getSolverFactory(
                                home.resolve(solver), getVersionString(solver, version, true)));
    }

    public List<String> getSupportedSolvers() {
        return installers.keySet().stream().collect(Collectors.toUnmodifiableList());
    }

    public List<Tuple2<String, List<String>>> getSupportedVersions()
            throws SmtLibSolverInstallerException {
        final var builder = ImmutableList.<Tuple2<String, List<String>>>builder();

        for (final var solver : getSupportedSolvers()) {
            builder.add(Tuple2.of(solver, getSupportedVersions(solver)));
        }

        return builder.build();
    }

    public List<String> getSupportedVersions(final String solver)
            throws SmtLibSolverInstallerException {
        if (!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return installers.get(solver).getSupportedVersions();
    }

    public List<Tuple2<String, List<String>>> getInstalledVersions()
            throws SmtLibSolverInstallerException {
        final var builder = ImmutableList.<Tuple2<String, List<String>>>builder();

        for (final var solver : getSupportedSolvers()) {
            builder.add(Tuple2.of(solver, getInstalledVersions(solver)));
        }

        return builder.build();
    }

    public List<String> getInstalledVersions(final String solver)
            throws SmtLibSolverInstallerException {
        if (!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return installers.get(solver).getInstalledVersions(home.resolve(solver));
    }

    public String getVersionString(
            final String solver, final String version, final boolean installed)
            throws SmtLibSolverInstallerException {
        if (!version.equals("latest")) {
            return version;
        } else {
            final var supportedVersions = getSupportedVersions(solver);
            final var versions =
                    installed
                            ? getInstalledVersions(solver).stream()
                                    .filter(supportedVersions::contains)
                                    .toList()
                            : supportedVersions;
            if (!versions.isEmpty()) {
                return versions.get(0);
            } else {
                throw new SmtLibSolverInstallerException(
                        String.format(
                                "There are no %s versions of solver: %s",
                                installed ? "installed" : "supported", solver));
            }
        }
    }

    @Override
    public void close() throws Exception {
        for (final var solver : instantiatedSolvers) {
            solver.close();
        }
        closed = true;
    }

    private final class ManagedFactory implements SolverFactory {

        private final SolverFactory solverFactory;

        private ManagedFactory(final SolverFactory solverFactory) {
            this.solverFactory = solverFactory;
        }

        @Override
        public Solver createSolver() {
            checkState(!closed, "Solver manager was closed");
            final var solver = solverFactory.createSolver();
            instantiatedSolvers.add(solver);
            return solver;
        }

        @Override
        public UCSolver createUCSolver() {
            checkState(!closed, "Solver manager was closed");
            final var solver = solverFactory.createUCSolver();
            instantiatedSolvers.add(solver);
            return solver;
        }

        @Override
        public ItpSolver createItpSolver() {
            checkState(!closed, "Solver manager was closed");
            final var solver = solverFactory.createItpSolver();
            instantiatedSolvers.add(solver);
            return solver;
        }

        @Override
        public HornSolver createHornSolver() {
            checkState(!closed, "Solver manager was closed");
            final var solver = solverFactory.createHornSolver();
            instantiatedSolvers.add(solver);
            return solver;
        }
    }
}
