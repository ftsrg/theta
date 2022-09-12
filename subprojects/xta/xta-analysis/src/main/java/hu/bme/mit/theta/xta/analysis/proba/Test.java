package hu.bme.mit.theta.xta.analysis.proba;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.NullLogger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;

import java.io.IOException;
import java.io.InputStream;


public class Test {

    public  String solver;
    public String filepath;
    public XtaConfigBuilder.Domain domain;
    public XtaConfigBuilder.Refinement refinement;


    private static Test instance;

    public static void main(String arg[]){
        instance = new Test();
        try {
            instance.check();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public void check() throws Exception {
        domain = XtaConfigBuilder.Domain.PRED_BOOL;
        refinement = XtaConfigBuilder.Refinement.FW_BIN_ITP;
        SolverManager.registerSolverManager(Z3SolverManager.create());
        if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
            SolverManager.registerSolverManager(SmtLibSolverManager.create(SmtLibSolverManager.HOME, NullLogger.getInstance()));
        }

        final SolverFactory solverFactory;

        solverFactory = SolverManager.resolveSolverFactory(solver);

        final InputStream inputStream = getClass().getResourceAsStream(filepath);
        XtaSystem system = XtaDslManager.createSystem(inputStream);

        XtaConfig<? extends State, ? extends Action, ? extends Prec> config =
                new XtaConfigBuilder(domain, refinement, solverFactory).build(system, null);
        SafetyResult<? extends State, ? extends Action> result = config.check();
        System.out.println(result.isSafe());
    }
}
