package hu.bme.mit.theta.xta.analysis.proba;

import hu.bme.mit.theta.analysis.Prec;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.xta.XtaProcess;

import java.util.Collection;

import static com.google.common.base.Preconditions.checkNotNull;

public class GlobalXtaPrec <P extends Prec> implements XtaPrec<P>{


    private final P prec;

    private GlobalXtaPrec(final P prec) {
        this.prec = checkNotNull(prec);
    }

    public static <P extends Prec> GlobalXtaPrec<P> create(final P prec) {
        return new GlobalXtaPrec<>(prec);
    }


    public P getPrec() {
        return prec;
    }

    public GlobalXtaPrec<P> refine(final P refinedPrec) {
        if (this.prec.equals(refinedPrec)) {
            return this;
        } else {
            return create(refinedPrec);
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(getClass().getSimpleName()).add(prec).toString();
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof GlobalXtaPrec) {
            final GlobalXtaPrec<?> that = (GlobalXtaPrec<?>) obj;
            return this.prec.equals(that.prec);
        } else {
            return false;
        }
    }
    @Override
    public int hashCode() {
        return 31 * prec.hashCode();
    }


    @Override
    public Collection<VarDecl<?>> getUsedVars() {
        return null;
    }

    @Override
    public P getPrec(XtaProcess.Loc loc) {
        return null;
    }
}
