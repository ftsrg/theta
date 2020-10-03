package hu.bme.mit.theta.mcm.dsl;

import hu.bme.mit.theta.mcm.MCM;
import hu.bme.mit.theta.mcm.dsl.gen.McmDslBaseVisitor;

public class McmParserVisitor extends McmDslBaseVisitor<> {


    private final MCM mcm;

    public McmParserVisitor() {
        this.mcm = new MCM();
    }

    public MCM getMcm() {
        return mcm;
    }
}
