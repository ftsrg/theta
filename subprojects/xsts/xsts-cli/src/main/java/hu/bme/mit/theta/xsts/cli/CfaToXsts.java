package hu.bme.mit.theta.xsts.cli;

import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.cfa.CFA;
import hu.bme.mit.theta.core.decl.Decls;
import hu.bme.mit.theta.core.stmt.*;
import hu.bme.mit.theta.xsts.XSTS;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static hu.bme.mit.theta.core.type.inttype.IntExprs.*;

public class CfaToXsts {

    public static XSTS create(CFA cfa){
        int i=0;
        final Map<CFA.Loc, Integer> map = new HashMap<>();
        for(var x : cfa.getLocs()){
            map.put(x,i++);
        }
        var locVar= Decls.Var("loc",Int());
        List<Stmt> tranList = cfa.getEdges().stream().map(e -> SequenceStmt.of(List.of(
                AssumeStmt.of(Eq(locVar.getRef(), Int(map.get(e.getSource())))),
                e.getStmt(),
                AssignStmt.of(locVar,Int(map.get(e.getTarget())))
        ))).collect(Collectors.toList());

        var tran= NonDetStmt.of(tranList);
        var initFormula=Eq(locVar.getRef(),Int(map.get(cfa.getInitLoc())));
        var prop=Neq(locVar.getRef(),Int(map.get(cfa.getErrorLoc())));
        var env =NonDetStmt.of(List.of(SkipStmt.getInstance()));
        var init=NonDetStmt.of(List.of(SkipStmt.getInstance()));
        return new XSTS(ImmutableMap.of(), Set.of(locVar),init,tran,env,initFormula,prop);
    }
}
