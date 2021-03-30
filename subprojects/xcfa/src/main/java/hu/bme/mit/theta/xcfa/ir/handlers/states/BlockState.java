package hu.bme.mit.theta.xcfa.ir.handlers.states;

import hu.bme.mit.theta.xcfa.model.XcfaLocation;

public class BlockState {
    private final FunctionState functionState;
    private int blockCnt = 0;
    private final String block;
    private XcfaLocation lastLocation;

    public BlockState(FunctionState functionState, String block) {
        this.functionState = functionState;
        this.block = block;
        lastLocation = functionState.getLocations().get(block);
    }

    public XcfaLocation getLastLocation() {
        return lastLocation;
    }

    public void setLastLocation(XcfaLocation lastLocation) {
        this.lastLocation = lastLocation;
    }

    public int getBlockCnt() {
        int cnt = blockCnt;
        ++blockCnt;
        return cnt;
    }

    public String getName() {
        return block;
    }

    public FunctionState getFunctionState() {
        return functionState;
    }
}
