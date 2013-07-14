package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.util.Triple;

public final class ClassWellDefinedness extends WellDefinednessCheck {

    final ClassInvariant inv;

    public ClassWellDefinedness(ClassInvariant inv, IObserverFunction target, Services services) {
        super(target, Type.CLASS_INVARIANT, services);
        assert inv != null;
        this.inv = inv;
        this.requires = inv.getOriginalInv();
        this.assignable = TB.func(services.getTypeConverter().getLocSetLDT().getAllLocs());
    }

    @Override
    public Type type() {
        return Type.CLASS_INVARIANT;
    }

    @Override
    public int id() {
        return inv.hashCode();
    }

    @Override
    public boolean transactionApplicableContract() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public String proofToString(Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Contract setID(int newId) {
        return this;
    }

    @Override
    public String getTypeName() {
        // TODO Auto-generated method stub
        return "Well-Definedness of " + inv.getDisplayName();
    }

    @Override
    public String getName() {
        return "Well-Definedness of " + inv.getName();
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
    public Triple<Term, ImmutableList<Term>, Term> createPOTerm() {
        Term inv = this.getRequires();
        ImmutableList<Term> c = ImmutableSLList.<Term>nil();
        c = c.append(this.getAssignable());
        return new Triple<Term, ImmutableList<Term>, Term>(inv, c, inv);
    }
}