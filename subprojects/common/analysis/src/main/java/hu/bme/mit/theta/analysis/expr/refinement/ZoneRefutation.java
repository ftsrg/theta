package hu.bme.mit.theta.analysis.expr.refinement;

import com.google.common.collect.ImmutableList;
import hu.bme.mit.theta.analysis.zone.DBM;
import hu.bme.mit.theta.analysis.zone.ZoneState;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

public class ZoneRefutation implements Refutation{

    private final int pruneIndex;
    private final List<ZoneState> zoneSequence;
    private final List<VarDecl<RatType>> clocks;


    private ZoneRefutation(){
        pruneIndex = -1;
        zoneSequence = Collections.emptyList();
        clocks = Collections.emptyList();
    }
    private ZoneRefutation(int prunIndex, List<ZoneState> zoneSequence, List<VarDecl<RatType>> clocks) {
        this.pruneIndex = prunIndex;
        this.zoneSequence= ImmutableList.copyOf(zoneSequence);
        this.clocks = clocks;
    }

    public static ZoneRefutation binary(final int pruneIndex, final ZoneState itpZone, List<VarDecl<RatType>> clocks, final int statecount)
    {
        final List<ZoneState> zoneSequence = new ArrayList<>();
        for (int i = 0; i < statecount; i ++){
            if(i < pruneIndex) {
                zoneSequence.add(ZoneState.top());
            }
            else if( i == pruneIndex){
                zoneSequence.add(itpZone);
            }
            else zoneSequence.add(ZoneState.bottom());
        }
        return new ZoneRefutation(pruneIndex, zoneSequence, clocks);
    }
    @Override
    public int getPruneIndex() {
        return this.pruneIndex;
    }

    public ZoneState get(int index){
        return zoneSequence.get(index);
    }

    public List<VarDecl<RatType>> getClocks() {
        return clocks;
    }

    public static ZoneRefutation emptyRefutation(){
        return new ZoneRefutation();
    }
}
