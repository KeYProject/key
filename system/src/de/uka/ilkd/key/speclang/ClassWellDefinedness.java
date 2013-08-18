package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;

public final class ClassWellDefinedness extends WellDefinednessCheck {

    private final ClassInvariant inv;

    private ClassWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                 LocationVariable heap, Precondition requires,
                                 Term assignable, Term ensures, ClassInvariant inv) {
        super(name, id, type, target, heap, requires, assignable, ensures);
        this.inv = inv;
    }

    public ClassWellDefinedness(ClassInvariant inv, IObserverFunction target, Services services) {
        super(inv.getName(), services.getSpecificationRepository().getInvCount(inv.getKJT()),
              target, Type.CLASS_INVARIANT, services);
        assert inv != null;
        this.inv = inv;
        this.setRequires(TB.tt());
        this.setAssignable(TB.func(services.getTypeConverter().getLocSetLDT().getAllLocs()));
        this.setEnsures(inv.getOriginalInv());
    }

    public ClassInvariant getInvariant() {
        return this.inv;
    }

    @Override
    public boolean transactionApplicableContract() {
        return false;
    }

    @Override
    public Contract setID(int newId) {
        return new ClassWellDefinedness(getName(),
                                        newId,
                                        type(),
                                        getTarget(),
                                        getHeap(),
                                        getRequires(),
                                        getAssignable(),
                                        getEnsures(),
                                        inv);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new ClassWellDefinedness(getName(),
                                        id(),
                                        type(),
                                        newPM,
                                        getHeap(),
                                        getRequires(),
                                        getAssignable(),
                                        getEnsures(),
                                        inv.setKJT(newKJT));
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

    @Override
    public POTerms createPOTerms() {
        Precondition pre = this.getRequires();
        final Term mod = this.getAssignable();
        final ImmutableList<Term> rest = ImmutableSLList.<Term>nil();
        Term post = this.getEnsures();
        return new POTerms(pre, mod, rest, post);
    }

    @Override
    public OriginalVariables getOrigVars() {
        assert getInvariant() != null;
        return getInvariant().getOrigVars();
    }
}