package hu.bme.mit.theta.xta.analysis;

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
import hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder_ClockPred;
import hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder_Zone;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import org.junit.Test;

import java.io.FileInputStream;
import java.io.InputStream;
import java.io.SequenceInputStream;

public class Test_ClockPred {
    public XtaConfigBuilder_ClockPred.Domain domain;

    public XtaConfigBuilder_ClockPred.Refinement refinement;

    private Test_ClockPred instance;

    @Test
    public void main(){
        instance = new Test_ClockPred();
        try{
            instance.check();
        }catch (Exception e){
            e.printStackTrace();
        }
    }

    public void check() throws Exception{
        domain = XtaConfigBuilder_ClockPred.Domain.PRED_CART;
        refinement = XtaConfigBuilder_ClockPred.Refinement.SEQ_ITP;
        SolverManager.registerSolverManager(Z3SolverManager.create());
        if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
            SolverManager.registerSolverManager(SmtLibSolverManager.create(SmtLibSolverManager.HOME, new ConsoleLogger(Logger.Level.DETAIL)));
        }

        final SolverFactory solverFactory;

        solverFactory = SolverManager.resolveSolverFactory("Z3");

        XtaSystem system;
        try(InputStream inputStream =  new SequenceInputStream(new FileInputStream("src/test/resources/model/ClockPredTest.xta"), new FileInputStream("src/test/resources/property/ClockPredTest.prop"))){
            system = XtaDslManager.createSystem(inputStream);
        }
        XtaConfigBuilder_ClockPred builder =  new XtaConfigBuilder_ClockPred(domain, refinement, /*solverFactory*/ Z3SolverFactory.getInstance());
        builder.precGranularity(XtaConfigBuilder_ClockPred.PrecGranularity.GLOBAL);
        builder.initPrec(XtaConfigBuilder_ClockPred.InitPrec.EMPTY);
        builder.maxEnum(1);

        XtaConfig config = builder.build(system);
        SafetyResult result = config.check();
        System.out.println("Safe?: " + result.isSafe());
    }
}
