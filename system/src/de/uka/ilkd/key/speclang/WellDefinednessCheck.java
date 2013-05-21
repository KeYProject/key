package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A contract for checking the well-definedness of a specification element
 * (i.e. a class invariant, a method contract, a loop invariant or a block contract),
 * consisting of bla bla bla.
 */
public abstract class WellDefinednessCheck implements Contract {

    protected static final TermBuilder TB = TermBuilder.DF;

    public final WellDefinednessCheck.Type type;

    private IObserverFunction target;

    private Term ensures;

    private Term assignable;

    public static enum Type {
        CLASS_INVARIANT, METHOD_CONTRACT, LOOP_INVARIANT, BLOCK_CONTRACT;
    }

    Type type() {
        return type;
    }

    WellDefinednessCheck(IObserverFunction target) {
        if (this instanceof MethodWellDefinedness) {
            type = Type.METHOD_CONTRACT;
        }/* else if (this instanceof ClassWellDefinedness) {
            type = Type.CLASS_INVARIANT;
        } else if (this instanceof LoopWellDefinedness) {
            type = Type.LOOP_INVARIANT;
        } else if (this instanceof BlockWellDefinedness) {
            type = Type.BLOCK_CONTRACT;
        }*/ else {
            type = null;
        }
        this.target = target;
    }

    public WellDefinednessCheck add(WellDefinednessCheck check) {
        this.ensures = TB.and(this.ensures, check.getEnsures());
        this.assignable = TB.and(this.assignable, check.getAssignable());
        return this;
    }

    public Term getEnsures() {
        return ensures;
    }

    public Term getAssignable() {
        return assignable;
    }

    @Override
    public IObserverFunction getTarget() {
        return target;
    }

    @Deprecated
    public boolean hasMby() {
        return false;
    }

    @Deprecated
    public Contract setTarget(KeYJavaType newKJT,
                              IObserverFunction newPM) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getPre(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getPre(List<LocationVariable> heapContext,
                       ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getPre(LocationVariable heap, Term heapTerm, Term selfTerm,
                       ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getPre(List<LocationVariable> heapContext,
                       Map<LocationVariable, Term> heapTerms, Term selfTerm,
                       ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getMby(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }

    @Deprecated
    public Term getMby(Term heapTerm, Term selfTerm, ImmutableList<Term> paramTerms,
                       Services services) throws UnsupportedOperationException {
        throw new UnsupportedOperationException("Not applicable for well-definedness checks.");
    }
}