package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermCreationException;
import de.uka.ilkd.key.logic.op.Equality;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Operator;

public class WellDefinednessOperator {

    public static final WellDefinednessOperator WD = new WellDefinednessOperator();

    public static final TermBuilder TB = TermBuilder.DF;
    
    public WellDefinednessOperator() {
    }

    // TODO: What about change of system state after valuation?
    public Term wd(Term t) {
        Operator op = t.op();
        int subs = t.arity();
        if (op.equals(Junctor.TRUE) || op.equals(Junctor.FALSE)) {
            assert subs == 0;
            return primaryExpr(t);
        } else if (op.equals(Junctor.NOT)) {
            assert subs == 1;
            return wd(t.sub(0));
        } else if (op.equals(Junctor.OR)) {
            assert subs == 2;
            return or(t.sub(0), t.sub(1));
        } else if (op.equals(Junctor.AND)) {
            assert subs == 2;
            return and(t.sub(0), t.sub(1));
        } else if (op.equals(Junctor.IMP)) {
            assert subs == 2;
            return imp(t.sub(0), t.sub(1));
        } else if (op.equals(Equality.EQV) || op.equals(Equality.EQUALS)) {
            assert subs == 2;
            return wd(t.sub(0), t.sub(1));
        } else if (op.name().toString().endsWith("<inv>")) {
            return inv(t);
        } // TODO: How to test if t is a fresh variable?
        else {
            throw new TermCreationException("Unknown term!" + '\n' +
                                            "Operator: " + op.toString() + '\n' +
                                            "Term: " + t.toString());
        }
    }

    private Term wd(Term a, Term b) {
        return TB.and(wd(a), wd(b));
    }

    // true, false
    private Term primaryExpr(Term a) {
        int subs = a.arity();
        assert subs == 0;
        return TB.tt();
    }

    // a || b
    private Term or(Term a, Term b) {
        Term guard = TB.and(wd(a), TB.equals(a, TB.tt()));
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    // a && b
    private Term and(Term a, Term b) {
        Term guard = TB.and(wd(a), TB.equals(a, TB.ff()));
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    // a ==> b
    private Term imp(Term a, Term b) {
        // What about a <== b ?
        Term guard = TB.and(wd(a), TB.equals(a, TB.ff()));
        Term wd = TB.and(wd(a), wd(b));
        return TB.or(guard, wd);
    }

    private Term inv(Term a) {
        return TB.tt();
    }
}
