package hu.bme.mit.theta.solver.smtlib.manager;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.common.Tuple2;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverInstaller;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverInstallerException;
import hu.bme.mit.theta.solver.smtlib.generic.GenericSmtLibSolverInstaller;

import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static com.google.common.base.Preconditions.checkState;

public final class SmtLibSolverManager {
    private static final Map<String, Class<? extends SmtLibSolverInstaller>> installerDeclarations = new HashMap<>();
    private static Tuple2<String, Class<? extends GenericSmtLibSolverInstaller>> genericInstallerDeclaration;

    public static <T extends SmtLibSolverInstaller> void registerInstaller(final String name, final Class<T> decl) {
        installerDeclarations.put(name, decl);
    }

    public static <T extends GenericSmtLibSolverInstaller> void registerGenericInstaller(final String name, final Class<T> decl) {
        checkState(genericInstallerDeclaration == null);
        genericInstallerDeclaration = Tuple2.of(name, decl);
    }

    static {
        registerGenericInstaller("generic", GenericSmtLibSolverInstaller.class);
    }

    private final Path home;
    private final Logger logger;

    private final Map<String, SmtLibSolverInstaller> installers;
    private final Tuple2<String, GenericSmtLibSolverInstaller> genericInstaller;

    private SmtLibSolverManager(final Path home, final Logger logger) {
        this.logger = logger;
        checkNotNull(home);
        checkArgument(Files.exists(home));

        this.home = home;

        try {
            this.genericInstaller = Tuple2.of(
                genericInstallerDeclaration.get1(),
                genericInstallerDeclaration.get2().getDeclaredConstructor(Logger.class).newInstance(logger)
            );

            this.installers = Stream.concat(
                Stream.of(this.genericInstaller),
                installerDeclarations.entrySet().stream()
                    .map(p -> {
                        try {
                            return Tuple2.of(p.getKey(), p.getValue().getDeclaredConstructor(Logger.class).newInstance(logger));
                        } catch (InstantiationException | IllegalAccessException | InvocationTargetException | NoSuchMethodException e) {
                            throw new RuntimeException(e);
                        }
                    })
            ).collect(Collectors.toUnmodifiableMap(Tuple2::get1, Tuple2::get2));
        } catch (InstantiationException | InvocationTargetException | NoSuchMethodException | IllegalAccessException e) {
            throw new RuntimeException(e);
        }

    }

    public static SmtLibSolverManager create(final Path home, final Logger logger) {
        return new SmtLibSolverManager(home, logger);
    }

    public String getGenericInstallerName() {
        return genericInstaller.get1();
    }

    public void install(final String solver, final String version) throws SmtLibSolverInstallerException {
        checkArgument(!solver.equals(genericInstaller.get1()));

        if(!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        final var installDir = home.resolve(solver);
        try {
            if (!Files.exists(installDir)) {
                Files.createDirectory(installDir);
            }
        } catch (IOException e) {
            throw new SmtLibSolverInstallerException(e);
        }

        installers.get(solver).install(installDir, version);
    }

    public void installGeneric(final String version, final Path solverPath, final String[] args) throws SmtLibSolverInstallerException {
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

    public void uninstall(final String solver, final String version) throws SmtLibSolverInstallerException {
        if(!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        installers.get(solver).uninstall(home.resolve(solver), version);
    }

    public void reinstall(final String solver, final String version) throws SmtLibSolverInstallerException {
        if(!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        installers.get(solver).reinstall(home.resolve(solver), version);
    }


    public String getInfo(final String solver, final String version) throws SmtLibSolverInstallerException {
        if(!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return installers.get(solver).getInfo(home.resolve(solver), version);
    }

    public Path getArgsFile(final String solver, final String version) throws SmtLibSolverInstallerException {
        if(!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return installers.get(solver).getArgsFile(home.resolve(solver), version);
    }

    public SolverFactory getSolverFactory(final String solver, final String version) throws SmtLibSolverInstallerException {
        if(!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return installers.get(solver).getSolverFactory(home.resolve(solver), version);
    }

    public List<String> getSupportedSolvers() throws SmtLibSolverInstallerException {
        return installers.keySet().stream().collect(Collectors.toUnmodifiableList());
    }

    public List<Tuple2<String, List<String>>> getSupportedVersions() throws SmtLibSolverInstallerException {
        final var builder = ImmutableList.<Tuple2<String, List<String>>>builder();

        for(final var solver : getSupportedSolvers()) {
            builder.add(Tuple2.of(solver, getSupportedVersions(solver)));
        }

        return builder.build();
    }

    public List<String> getSupportedVersions(final String solver) throws SmtLibSolverInstallerException {
        if(!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return installers.get(solver).getSupportedVersions();
    }

    public List<Tuple2<String, List<String>>> getInstalledVersions() throws SmtLibSolverInstallerException {
        final var builder = ImmutableList.<Tuple2<String, List<String>>>builder();

        for(final var solver : getSupportedSolvers()) {
            builder.add(Tuple2.of(solver, getInstalledVersions(solver)));
        }

        return builder.build();
    }

    public List<String> getInstalledVersions(final String solver) throws SmtLibSolverInstallerException {
        if(!installers.containsKey(solver)) {
            throw new SmtLibSolverInstallerException(String.format("Unknown solver: %s", solver));
        }

        return installers.get(solver).getInstalledVersions(home.resolve(solver));
    }
}
