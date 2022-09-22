package hu.bme.mit.theta.xta.analysis;

import hu.bme.mit.theta.analysis.Action;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.solver.z3.Z3SolverFactory;
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

        XtaSystem system;
        try( InputStream inputStream =  new SequenceInputStream(new FileInputStream("src/test/resources/model/AndOr.xta"), new FileInputStream("src/test/resources/property/AndOr.prop"))){
            system = XtaDslManager.createSystem(inputStream);
        }


        XtaConfig<? extends State, ? extends Action, ? extends Prec> config =
                new XtaConfigBuilder(domain, refinement, Z3SolverFactory.getInstance()).build(system, null);
        SafetyResult<? extends State, ? extends Action> result = config.check();
        System.out.println("Safe? : " + result.isSafe());
    }
}
