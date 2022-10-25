package hu.bme.mit.theta.xta.analysis.prec;

import com.google.common.collect.ImmutableMap;
import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.analysis.pred.PredPrec;
import hu.bme.mit.theta.analysis.prod2.Prod2Prec;
import hu.bme.mit.theta.analysis.zone.ZonePrec;
import hu.bme.mit.theta.common.container.Containers;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xta.XtaProcess;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static com.google.common.base.Preconditions.checkNotNull;

public class LocalXtaPrec<P extends Prec> implements XtaPrec<P>{


    private final Map<XtaProcess.Loc, P> mapping;

    private final Optional<P> defaultPrec;

    private LocalXtaPrec(final Map<XtaProcess.Loc, P> mapping, final Optional<P> defaultPrec) {
        this.defaultPrec = defaultPrec;

        final ImmutableMap.Builder<XtaProcess.Loc, P> builder = ImmutableMap.builder();
        for (final Map.Entry<XtaProcess.Loc, P> entry : mapping.entrySet()) {
            if (!defaultPrec.isPresent() || !defaultPrec.get().equals(entry.getValue())) {
                builder.put(entry);
            }
        }
        this.mapping = builder.build();
    }



    public static <P extends Prec> LocalXtaPrec<P> create(final P defaultPrec) {
        return new LocalXtaPrec<>(Collections.emptyMap(), Optional.of(defaultPrec));
    }

    public static <P extends Prec> LocalXtaPrec<P> create(final Map<XtaProcess.Loc, P> mapping, final P defaultPrec) {
        return new LocalXtaPrec<>(mapping, Optional.of(defaultPrec));
    }


    @Override
    public Collection<VarDecl<?>> getUsedVars() {
        return defaultPrec.get().getUsedVars();
    }

    @Override
    public Prec join(Prec other) {
        if(other instanceof LocalXtaPrec<?> other1){
            for(Map.Entry<XtaProcess.Loc, P> entry: mapping.entrySet()){
                entry.getValue().join((P) other1.mapping.get(entry.getKey()));
            }
            return this;
        }
        else{
            throw  new IllegalArgumentException("Only the same precision types can be joined");
        }
    }



    @Override
    public  P getPrec(Collection<XtaProcess.Loc> locs) {
        List<P> precs = locs.stream().map(loc -> mapping.get(loc)).collect(Collectors.toList());
        while(precs.remove(null));
        return precs.stream().reduce((P p1, P p2) -> (P) p1.join(p2)).get();
    }

    public LocalXtaPrec<P> refine (final Map<XtaProcess.Loc, P> refinedPrecs){
        checkNotNull(refinedPrecs);



        final Map<XtaProcess.Loc, P> refinedMapping = Containers.createMap(this.mapping);

        for (final Map.Entry<XtaProcess.Loc, P> entry : refinedPrecs.entrySet()) {
            final XtaProcess.Loc loc = entry.getKey();
            final P prec = entry.getValue();

            if (defaultPrec.isPresent() && !mapping.containsKey(loc) && defaultPrec.get() == prec) {
                continue;
            }
            if(mapping.get(loc) == null) refinedMapping.put(loc,prec);
           else refinedMapping.put(loc, (P) mapping.get(loc).join(prec));
        }
        return new LocalXtaPrec<>(refinedMapping, this.defaultPrec);
    }
}
