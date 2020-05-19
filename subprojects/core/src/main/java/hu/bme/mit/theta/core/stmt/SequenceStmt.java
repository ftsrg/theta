package hu.bme.mit.theta.core.stmt;

import hu.bme.mit.theta.common.Utils;

import java.util.List;

public class SequenceStmt implements Stmt{

    private List<Stmt> stmts;

    private static final int HASH_SEED = 241;
    private static final String STMT_LABEL = "sequence";

    private volatile int hashCode = 0;

    private SequenceStmt(List<Stmt> stmts){
        this.stmts=stmts;
        if(stmts.isEmpty()) stmts.add(SkipStmt.getInstance());
    }

    public static SequenceStmt of(List<Stmt> stmts){
        return new SequenceStmt(stmts);
    }

    public List<Stmt> getStmts(){
        return stmts;
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
            result = 31 * result + stmts.hashCode();
            hashCode = result;
        }
        return result;
    }

    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        } else if (obj instanceof SequenceStmt) {
            final SequenceStmt that = (SequenceStmt) obj;
            return this.getStmts().equals(that.getStmts());
        } else {
            return false;
        }
    }

    @Override
    public String toString() {
        return Utils.lispStringBuilder().addAll(stmts).toString();
    }

}
