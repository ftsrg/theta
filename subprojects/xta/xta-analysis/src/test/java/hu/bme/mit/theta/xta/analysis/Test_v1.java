package hu.bme.mit.theta.xta.analysis;

import hu.bme.mit.theta.analysis.Cex;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.algorithm.Proof;
import hu.bme.mit.theta.analysis.algorithm.SafetyResult;
import hu.bme.mit.theta.solver.z3legacy.Z3LegacySolverFactory;
import hu.bme.mit.theta.xta.XtaSystem;
import hu.bme.mit.theta.xta.analysis.config.XtaConfig;
import hu.bme.mit.theta.xta.analysis.config.XtaConfigBuilder;
import hu.bme.mit.theta.xta.dsl.XtaDslManager;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStream;
import java.io.SequenceInputStream;
import org.junit.jupiter.api.Test;

public final class Test_v1 {
    public  String solver;
    public String filepath;
    public XtaConfigBuilder.Domain domain;
    public XtaConfigBuilder.Refinement refinement;

    @Test
    public void check() throws IOException {
        domain = XtaConfigBuilder.Domain.PRED_CART;
        refinement = XtaConfigBuilder.Refinement.SEQ_ITP;

        InputStream inputStream =  new SequenceInputStream(
            new FileInputStream("src/test/resources/model/AndOr.xta"),
            new FileInputStream("src/test/resources/property/AndOr.prop")
        );
        XtaSystem system = XtaDslManager.createSystem(inputStream);

        XtaConfig<? extends Proof, ? extends Cex, ? extends Prec> config =
                new XtaConfigBuilder(domain, refinement, Z3LegacySolverFactory.getInstance())
                        .build(system, null);
        SafetyResult<? extends Proof, ? extends Cex> result = config.check();
        System.out.println("Safe? : " + result.isSafe());
    }
}
