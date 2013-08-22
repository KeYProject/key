package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;

public final class ClassWellDefinedness extends WellDefinednessCheck {

    private final ClassInvariant inv;
    private final boolean model;

    private ClassWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                 LocationVariable heap, OriginalVariables origVars,
                                 Precondition requires, Term assignable, Term accessible,
                                 Term ensures, Term mby, Term rep, ClassInvariant inv, boolean model) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
        this.inv = inv;
        this.model = model;
    }

    public ClassWellDefinedness(ClassInvariant inv, IObserverFunction target,
                                Term accessible, Term mby, boolean model, Services services) {
        super("JML " + (model ? "model " : "") + "class invariant in " + inv.getKJT().getName(),
              services.getSpecificationRepository().getInvCount(inv.getKJT()), target,
              inv.getOrigVars(), Type.CLASS_INVARIANT, services);
        assert inv != null;
        this.inv = inv;
        this.model = model;
        setRequires(TB.tt());
        setAssignable(TB.func(services.getTypeConverter().getLocSetLDT().getEmpty()));
        setEnsures(inv.getOriginalInv());
        setAccessible(accessible);
        setMby(mby);
    }

    @Override
    TermAndFunc generateMbyAtPreDef(ParsableVariable self,
                                    ImmutableList<ParsableVariable> params,
                                    Services services) {
        return new TermAndFunc(TB.tt(), null);
    }

    @Override
    ImmutableList<Term> getRest() {
        return super.getRest();
    }

    public ClassInvariant getInvariant() {
        return this.inv;
    }

    @Override
    public boolean isModel() {
        return this.model;
    }

    @Override
    public boolean transactionApplicableContract() {
        return false;
    }

    @Override
    public ClassWellDefinedness setID(int newId) {
        return new ClassWellDefinedness(getName(), newId, type(), getTarget(), getHeap(),
                                        getOrigVars(), getRequires(), getAssignable(),
                                        getAccessible(), getEnsures(), getMby(),
                                        getRepresents(), getInvariant(), isModel());
    }

    @Override
    public ClassWellDefinedness setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new ClassWellDefinedness(getName(), id(), type(), newPM, getHeap(),
                                        getOrigVars(), getRequires(), getAssignable(),
                                        getAccessible(), getEnsures(), getMby(),
                                        getRepresents(), getInvariant().setKJT(newKJT),
                                        isModel());
    }

    @Override
    public String getTypeName() {
        return "Well-Definedness of " + (isModel() ? "model " : "") + inv.getDisplayName();
    }

    @Override
    public VisibilityModifier getVisibility() {
        return inv.getVisibility();
    }

    @Override
    public KeYJavaType getKJT() {
        return inv.getKJT();
    }

    @Override
    public Term getGlobalDefs() {
        throw new UnsupportedOperationException("Not applicable for well-definedness of invariants.");
    }
}