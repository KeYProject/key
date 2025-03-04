package de.uka.ilkd.key.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.expression.Operator;
import de.uka.ilkd.key.java.expression.literal.EmptyMSetLiteral;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.operator.adt.*;
import de.uka.ilkd.key.java.expression.operator.mst.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.JFunction;

import org.key_project.logic.Name;
import org.key_project.util.ExtList;

public class MSetLDT extends LDT {

    public static final Name NAME = new Name("Mset");

    private final JFunction msetRange;
    private final JFunction msetMul;
    private final JFunction msetEmpty;
    private final JFunction msetSingle;
    private final JFunction msetUnion;
    private final JFunction msetIntersec;
    private final JFunction msetSum;
    private final JFunction msetDiff;
    private final JFunction msetCard;

    public MSetLDT(TermServices services) {
        super(NAME, services);
        msetMul = addFunction(services, "msetMul");
        msetEmpty = addFunction(services, "msetEmpty");
        msetSingle = addFunction(services, "msetSingle");
        msetUnion = addFunction(services, "msetUnion");
        msetIntersec = addFunction(services, "msetIntersec");
        msetSum = addFunction(services, "msetSum");
        msetDiff = addFunction(services, "msetDiff");
        msetCard = addFunction(services, "msetCard");
        msetRange = addFunction(services , "msetRange");
    }


    public JFunction getMsetRange(){ return msetRange;}
    public JFunction getMsetMul() {
        return msetMul;
    }

    public JFunction getMsetEmpty() {
        return msetEmpty;
    }

    public JFunction getMsetSingle() {
        return msetSingle;
    }

    public JFunction getMsetUnion() {
        return msetUnion;
    }

    public JFunction getMsetIntersec() {
        return msetIntersec;
    }

    public JFunction getMsetAdd() {
        return msetSum;
    }

    public JFunction getMsetRemove() {
        return msetDiff;
    }
    @Override
    public boolean isResponsible(Operator op, Term[] subs, Services services, ExecutionContext ec) {
       return op instanceof MSetCard || op instanceof MSetMul || op instanceof MSetSingle || op instanceof MSetIntersect ||
               op instanceof MSetDiff || op instanceof MSetUnion || op instanceof MSetSum;
    }

    @Override
    public boolean isResponsible(Operator op, Term left, Term right, Services services, ExecutionContext ec) {
        return op instanceof MSetUnion || op instanceof MSetIntersect || op instanceof MSetSum || op instanceof MSetDiff;
    }

    @Override
    public boolean isResponsible(Operator op, Term sub, TermServices services, ExecutionContext ec) {
        return op instanceof MSetSingle || op instanceof MSetMul || op instanceof MSetCard;
    }

    @Override
    public Term translateLiteral(Literal lit, Services services) {
        assert lit instanceof EmptySeqLiteral;
        return services.getTermBuilder().func(msetEmpty);
    }

    @Override
    public JFunction getFunctionFor(Operator op, Services services, ExecutionContext ec) {
        if (op instanceof MSetSingle) {
            return msetSingle;
        } else if (op instanceof MSetCard) {
            return msetCard;
        } else if (op instanceof MSetUnion) {
            return msetUnion;
        } else if (op instanceof MSetDiff) {
            return msetDiff;
        } else if (op instanceof MSetSum) {
            return msetSum;
        } else if (op instanceof MSetIntersect) {
            return msetIntersec;
        } else if (op instanceof MSetMul) {
            return msetMul;
        }

        assert false;
        return null;

    }

    @Override
    public boolean hasLiteralFunction(JFunction f) {
        return f.equals(msetEmpty);
    }

    @Override
    public Expression translateTerm(Term t, ExtList children, Services services) {
        if (t.op().equals(msetEmpty)) {
            return EmptyMSetLiteral.INSTANCE;
        }
        assert false;
        return null;    }

    @Override
    public Type getType(Term t) {
       assert false;
        return null;
    }
}
