package hu.bme.mit.theta.analysis.zone;

import com.google.common.collect.ImmutableSet;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.rattype.RatType;

import java.util.*;
import java.util.stream.Collectors;

import static com.google.common.base.Preconditions.checkNotNull;

public class ClockPredPrec  implements Prec{

    private final Map<Pair<VarDecl<RatType>, VarDecl<RatType>>, Set<Integer>> map;
    private final Set<VarDecl<RatType>> clocks;

    private ClockPredPrec(final Map<Pair<VarDecl<RatType>, VarDecl<RatType>>,  Set<Integer>> map, final Collection<? extends VarDecl<RatType>> clocks){
        checkNotNull(clocks);
        this.clocks = ImmutableSet.copyOf(clocks);
        this.map = map;
        sort();
    }


    public static ClockPredPrec of(final Collection<? extends VarDecl<RatType>> clocks) {
        return ClockPredPrec.emptyPrec(clocks);
    }


    public static ClockPredPrec emptyPrec(final Collection<? extends VarDecl<RatType>> clocks){
        Map<Pair<VarDecl<RatType>, VarDecl<RatType>>, Set<Integer>> empty = new HashMap<>();
        return new ClockPredPrec(empty, clocks);
    }

    public Set<VarDecl<RatType>> getVars() {
        return clocks;
    }
    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName()).addAll(clocks).toString();
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof ClockPredPrec) {
            final ClockPredPrec that = (ClockPredPrec) obj;
            return this.getVars().equals(that.getVars());
        } else {
            return false;
        }
    }

    public Collection<VarDecl<?>> getUsedVars() { // This could be way more elegant
        return clocks.stream().map(ratTypeVarDecl -> (VarDecl<?>) ratTypeVarDecl).collect(Collectors.toSet());
    }
    @Override
    public int hashCode() {
        return 31 * clocks.hashCode();
    }



    public static ClockPredPrec of(final Map<Pair<VarDecl<RatType>, VarDecl<RatType>>,  Set<Integer>> map, final Collection<? extends VarDecl<RatType>> clocks) {
        //checknotnull
        return new ClockPredPrec(map, clocks);
    }



    public ClockPredPrec join(final ClockPredPrec other){
        //addClocks(other.getVars());
        for(Map.Entry<Pair<VarDecl<RatType>, VarDecl<RatType>>,  Set<Integer>> entry: other.map.entrySet()){
            if(map.containsKey(entry.getKey())){
                map.get(entry.getKey()).addAll(entry.getValue());
            }
            else{
                map.put(entry.getKey(), entry.getValue());
            }
        }

        sort();
        return this;
    }

    @Override
    public Prec join(Prec other) {
        if(this == other)return this;
        if(other instanceof ClockPredPrec other1){
            return join(other1);
        }
        else{
            throw new IllegalArgumentException();
        }
    }
    public Map<Pair<VarDecl<RatType>, VarDecl<RatType>>,  Set<Integer>> getPreds(){
        sort(); return map;
    }


    private void sort(){
       for (Pair<VarDecl<RatType>, VarDecl<RatType>> k: map.keySet()){
           map.get(k).stream().sorted();
       }
    }

    public void add(VarDecl<RatType> x, Integer b){
        Pair<VarDecl<RatType>,VarDecl<RatType>> key = new Pair<>(x);
        if(!map.containsKey(key)){
            map.put(key, new HashSet<Integer>());
        }
        map.get(key).add(b);

    }
    public void add(VarDecl<RatType> x, VarDecl<RatType> y,Integer b){
        Pair<VarDecl<RatType>,VarDecl<RatType>> key = new Pair<>(x,y);
        if(!map.containsKey(key)){
            map.put(key, new HashSet<Integer>());
        }
        map.get(key).add(b);

    }


}
