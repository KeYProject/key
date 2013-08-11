package de.uka.ilkd.key.speclang;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

public final class ClassInvWellDefinedness extends WellDefinednessCheck {

    private final ClassInvariant inv;

    public ClassInvWellDefinedness(ClassInvariant inv, IObserverFunction target, Services services) {
        super(inv.getName(), target, Type.CLASS_INVARIANT, services);
        assert inv != null;
        this.inv = inv;
        this.setRequires(TB.tt());
        this.setAssignable(TB.func(services.getTypeConverter().getLocSetLDT().getAllLocs()));
        this.setEnsures(inv.getOriginalInv());
    }

    private ClassInvWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                    LocationVariable heap, Term implicitRequires,
                                    Term requires, Term assignable, Term ensures,
                                    ClassInvariant inv) {
        super(name, id, type, target, heap, implicitRequires, requires, assignable, ensures);
        this.inv = inv;
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
        return new ClassInvWellDefinedness(getName(),
                                           newId,
                                           type(),
                                           getTarget(),
                                           getHeap(),
                                           implicitRequires(),
                                           requires(),
                                           getAssignable(),
                                           getEnsures(),
                                           inv);
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
    public Triple<Pair<Term, Term>, ImmutableList<Term>, Term> createPOTerm() {
        Pair<Term, Term> pre = this.getRequires();
        ImmutableList<Term> c = ImmutableSLList.<Term>nil();
        c = c.append(this.getAssignable());
        Term inv = this.getEnsures();
        return new Triple<Pair<Term, Term>, ImmutableList<Term>, Term>(pre, c, inv);
    }

    public Taclet getTaclet(Services services) {
        IObserverFunction target = getTarget();
        boolean isStatic = target.isStatic();
        KeYJavaType kjt = inv.getKJT();
        TacletGenerator TG = TacletGenerator.getInstance();

        Name name = MiscTools.toValidTacletName("wd invariant "
                                                + (isStatic ? "static ": "")
                                                + target.name().toString());

        //create schema variables
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final List<SchemaVariable> heapSVs = new LinkedList<SchemaVariable>();
        final List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        for(int j = 0; j< heaps.size(); j++) {
            heapSVs.add(SchemaVariableFactory.createTermSV(new Name("h"+j),
                                                           heapLDT.targetSort(),
                                                           false,
                                                           false));
        }
        final SchemaVariable selfSV = isStatic ?
                null : SchemaVariableFactory.createTermSV(new Name("self"), kjt.getSort());
        final Taclet taclet = TG.generateWdInvTaclet(name,
                                                     heapSVs,
                                                     selfSV,
                                                     inv.getInv(selfSV, services),
                                                     getRequires(null),
                                                     kjt,
                                                     isStatic,
                                                     services);
        return taclet;
    }

    @Override
    public OriginalVariables getOrigVars() {
        assert getInvariant() != null;
        return getInvariant().getOrigVars();
    }
}