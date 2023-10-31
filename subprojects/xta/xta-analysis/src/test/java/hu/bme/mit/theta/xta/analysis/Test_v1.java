package hu.bme.mit.theta.xta.analysis;

import hu.bme.mit.theta.common.OsHelper;
import hu.bme.mit.theta.common.logging.ConsoleLogger;
import hu.bme.mit.theta.common.logging.Logger;
import hu.bme.mit.theta.solver.SolverFactory;
import hu.bme.mit.theta.solver.SolverManager;
import hu.bme.mit.theta.solver.smtlib.SmtLibSolverManager;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
import hu.bme.mit.theta.solver.z3.Z3SolverManager;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder_Zone;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import org.junit.Test;

import java.io.FileInputStream;
import java.io.InputStream;
import java.io.SequenceInputStream;

public class Test_v1 {
    public  String solver;
    public String filepath;
    public XtaConfigBuilder_Zone.Domain dataDomain;
    public XtaConfigBuilder_Zone.Refinement refinement;


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
        dataDomain = XtaConfigBuilder_Zone.Domain.PRED_CART;
        refinement = XtaConfigBuilder_Zone.Refinement.SEQ_ITP;
        SolverManager.registerSolverManager(Z3SolverManager.create());
        if(OsHelper.getOs().equals(OsHelper.OperatingSystem.LINUX)) {
            SolverManager.registerSolverManager(SmtLibSolverManager.create(SmtLibSolverManager.HOME, new ConsoleLogger(Logger.Level.DETAIL)));
        }

        final SolverFactory solverFactory;

        solverFactory = SolverManager.resolveSolverFactory("Z3");

        XtaSystem system;
       try( InputStream inputStream =  new SequenceInputStream(new FileInputStream("src/test/resources/model/ClockPredTest.xta"), new FileInputStream("src/test/resources/property/ClockPredTest.prop"))){
            system = XtaDslManager.createSystem(inputStream);
        }
        /*try( InputStream inputStream =  new SequenceInputStream(new FileInputStream("src/test/resources/model/mytest.xta"), new FileInputStream("src/test/resources/property/mytest.prop"))){
            system = XtaDslManager.createSystem(inputStream);
        }*/

        XtaConfigBuilder_Zone builder =  new XtaConfigBuilder_Zone(dataDomain, refinement, /*solverFactory*/ Z3SolverFactory.getInstance());
        builder.precGranularity(XtaConfigBuilder_Zone.PrecGranularity.GLOBAL);
        builder.initPrec(XtaConfigBuilder_Zone.InitPrec.EMPTY);
        builder.maxEnum(1);
        /*XtaConfig<? extends State, ? extends Action, ? extends Prec> config =
                builder.build(system);
        SafetyResult<? extends State, ? extends Action> result = config.check();
        System.out.println("Safe? : " + result.isSafe());*/

    }
}