package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.common.Utils;
import hu.bme.mit.theta.core.decl.VarDecl;
import hu.bme.mit.theta.core.type.clocktype.ClockType;

import static com.google.common.base.Preconditions.checkNotNull;

public final class ResetStmt implements Stmt {

    private static final int HASH_SEED = 6141;
    private static final String STMT_LABEL = "reset";

    private final VarDecl<ClockType> clock;
    private final int value;

    private volatile int hashCode = 0;

    private ResetStmt(final VarDecl<ClockType> clock, final int value) {
        this.clock = checkNotNull(clock);
        this.value = value;
    }

    public static ResetStmt of(final VarDecl<ClockType> clock, int value) {
        return new ResetStmt(clock, value);
    }

    public VarDecl<ClockType> getClockDecl() {
        return clock;
    }

    public int getValue() {
        return value;
    }

    @Override
    public <P, R> R accept(final StmtVisitor<? super P, ? extends R> visitor, final P param) {
        return visitor.visit(this, param);
    }

    @Override
    public int hashCode() {
        int result = hashCode;
        if (result == 0) {
            result = HASH_SEED;
            result = 31 * result + clock.hashCode();
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof ResetStmt) {
            final ResetStmt that = (ResetStmt) obj;
            return this.getClockDecl().equals(that.getClockDecl()) && this.value == that.value;
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder(STMT_LABEL).add(clock.getName()).add(value).toString();
    }
}
