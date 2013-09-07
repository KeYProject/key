package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

/**
 * A contract for checking the well-definedness of a jml loop invariant.
 *
 * @author Michael Kirsten
 */
public class LoopWellDefinedness extends StatementWellDefinedness {

    private final LoopInvariant inv;

    private LoopWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                LocationVariable heap, OriginalVariables origVars,
                                Condition requires, Term assignable, Term accessible,
                                Condition ensures, Term mby, Term rep, LoopInvariant inv) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
        this.inv = inv;
    }

    public LoopWellDefinedness(LoopInvariant inv, ImmutableSet<ProgramVariable> params,
                               Services services) {
        super(inv.getName(), inv.getLoop().getStartPosition().getLine(), inv.getTarget(),
              inv.getOrigVars().add(convertParams(params)), Type.LOOP_INVARIANT, services);
        assert inv != null;
        final LocationVariable h = getHeap();
        this.inv = inv;
        setMby(inv.getInternalVariant());
        setRequires(inv.getInternalInvariants().get(h));
        setAssignable(inv.getInternalModifies().get(h), services);
        setEnsures(inv.getInternalInvariants().get(h));
    }

    SequentFormula generateSequent(SequentTerms seq, Services services) {
        // wd(phi) & (phi & wf(anon) -> wd(mod) & wd(variant) & {anon^mod}(wd(phi) & wd(variant)))
        final Term imp = TB.imp(TB.and(seq.pre, seq.wfAnon),
                                TB.and(seq.wdMod, seq.wdRest, seq.anonWdPost));
        final Term wdPre = TB.wd(seq.pre, services);
        return new SequentFormula(TB.apply(seq.context,
                                           TB.and(wdPre, imp)));
    }

    public LoopInvariant getStatement() {
        return this.inv;
    }

    @Override
    public boolean transactionApplicableContract() {
        return false;
    }

    @Override
    public Contract setID(int newId) {
        return new LoopWellDefinedness(getName(), newId, type(), getTarget(), getHeap(),
                                       getOrigVars(), getRequires(), getAssignable(),
                                       getAccessible(), getEnsures(), getMby(),
                                       getRepresents(), getStatement());
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new LoopWellDefinedness(getName(), id(), type(), newPM, getHeap(),
                                       getOrigVars(), getRequires(), getAssignable(),
                                       getAccessible(), getEnsures(), getMby(),
                                       getRepresents(), getStatement().setTarget(newKJT, newPM));
    }

    @Override
    public String getTypeName() {
        return "Well-Definedness of " + inv.getDisplayName();
    }

    @Override
    public VisibilityModifier getVisibility() {
        return inv.getVisibility();
    }

    @Override
    public KeYJavaType getKJT() {
        return inv.getKJT();
    }
}