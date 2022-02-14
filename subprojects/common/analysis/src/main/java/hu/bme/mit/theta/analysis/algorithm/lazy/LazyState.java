package hu.bme.mit.theta.analysis.algorithm.lazy;

import hu.bme.mit.theta.analysis.State;
import hu.bme.mit.theta.analysis.expr.ExprState;
import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.type.Expr;
import hu.bme.mit.theta.core.type.booltype.BoolType;

import static com.google.common.base.Preconditions.checkArgument;
import static com.google.common.base.Preconditions.checkNotNull;
import static hu.bme.mit.theta.core.type.booltype.BoolExprs.False;

public abstract class ItpState<SConcr extends State, SAbstr extends ExprState> implements ExprState {

    private ItpState(){
    }

    public static <SConcr extends State, SAbstr extends ExprState> ItpState<SConcr, SAbstr> of(final SConcr concrState, final SAbstr abstrState) {
        if (concrState.isBottom()) {
            return new Bottom<>(concrState);
        } else {
            return new NonBottom<>(concrState, abstrState);
        }
    }

    public static <SConcr extends State, SAbstr extends ExprState> ItpState<SConcr, SAbstr> of(final SConcr state, final InitAbstractor<SConcr, SAbstr> initAbstractor) {
        if (state.isBottom()) {
            return new Bottom<>(state);
        } else {
            return new NonBottom<>(state, initAbstractor.getInitAbstrState(state));
        }
    }

    public abstract SConcr getConcrState();

    public abstract SAbstr getAbstrState();

    public abstract ItpState<SConcr, SAbstr> withConcrState(final SConcr concrState);

    public abstract ItpState<SConcr, SAbstr> withAbstrState(final SAbstr abstrState);

    private static final class NonBottom<SConcr extends State, SAbstr extends ExprState> extends ItpState<SConcr, SAbstr> {

        private final SConcr concrState;
        private final SAbstr abstrState;

        private NonBottom(final SConcr concrState, final SAbstr abstrState) {
            this.concrState = checkNotNull(concrState);
            this.abstrState = checkNotNull(abstrState);
        }

        @Override
        public SConcr getConcrState() {
            return concrState;
        }

        @Override
        public SAbstr getAbstrState() {
            return abstrState;
        }

        @Override
        public ItpState<SConcr, SAbstr> withConcrState(final SConcr concrState) {
            return ItpState.of(concrState, abstrState);
        }

        @Override
        public ItpState<SConcr, SAbstr> withAbstrState(final SAbstr abstrState) {
            return ItpState.of(concrState, abstrState);
        }

        @Override
        public boolean isBottom() {
            return false;
        }

        @Override
        public Expr<BoolType> toExpr() {
            return abstrState.toExpr();
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(ItpState.class.getSimpleName()).aligned()
                    .add(concrState.toString())
                    .add(abstrState.toString())
                    .toString();
        }
    }

    private static final class Bottom<SConcr extends State, SAbstr extends ExprState> extends ItpState<SConcr, SAbstr> {

        private final SConcr state;

        private Bottom(final SConcr state) {
            this.state = checkNotNull(state);
        }

        @Override
        public SConcr getConcrState() {
            return state;
        }

        @Override
        public SAbstr getAbstrState() {
            throw new UnsupportedOperationException();
        }

        @Override
        public ItpState<SConcr, SAbstr> withConcrState(final SConcr concrState) {
            checkArgument(concrState.isBottom());
            return this;
        }

        @Override
        public ItpState<SConcr, SAbstr> withAbstrState(final SAbstr abstrState) {
            return this;
        }

        @Override
        public boolean isBottom() {
            return true;
        }

        @Override
        public Expr<BoolType> toExpr() {
            return False();
        }

        @Override
        public String toString() {
            return Utils.lispStringBuilder(ItpState.class.getSimpleName()).aligned()
                    .add(state.toString())
                    .toString();
        }
    }
}


