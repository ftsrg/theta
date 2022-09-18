package hu.bme.mit.theta.xta.analysis;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.config.XtaConfig;
import hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import org.junit.Test;

import java.io.FileInputStream;
import java.io.InputStream;
import java.io.SequenceInputStream;

public class Test_v1 {
    public  String solver;
    public String filepath;
    public XtaConfigBuilder.Domain domain;
    public XtaConfigBuilder.Refinement refinement;


    private Test_v1 instance;

    @Test
    public void main(){
        instance = new Test_v1();
        try {
            instance.check();
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

    public void check() throws Exception {
        domain = XtaConfigBuilder.Domain.PRED_CART;
        refinement = XtaConfigBuilder.Refinement.SEQ_ITP;
        SolverManager.registerSolverManager(Z3SolverManager.create());
        if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
            SolverManager.registerSolverManager(SmtLibSolverManager.create(SmtLibSolverManager.HOME, new ConsoleLogger(Logger.Level.DETAIL)));
        }

        final SolverFactory solverFactory;

        solverFactory = SolverManager.resolveSolverFactory("Z3");

        XtaSystem system;
        try( InputStream inputStream =  new SequenceInputStream(new FileInputStream("src/test/resources/model/mytest.xta"), new FileInputStream("src/test/resources/property/mytest.prop"))){
            system = XtaDslManager.createSystem(inputStream);
        }


        XtaConfig<? extends State, ? extends Action, ? extends Prec> config =
                new XtaConfigBuilder(domain, refinement, /*solverFactory*/ Z3SolverFactory.getInstance()).build(system, null);
        SafetyResult<? extends State, ? extends Action> result = config.check();
        System.out.println("Safe? : " + result.isSafe());
    }
}
