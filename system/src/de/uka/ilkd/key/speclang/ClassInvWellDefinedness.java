package de.uka.ilkd.key.speclang;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.TacletGenerator;
import de.uka.ilkd.key.util.MiscTools;
import de.uka.ilkd.key.util.Triple;

public final class ClassInvWellDefinedness extends WellDefinednessCheck {

    final ClassInvariant inv;

    public ClassInvWellDefinedness(ClassInvariant inv, IObserverFunction target, Services services) {
        super(target, Type.CLASS_INVARIANT, services);
        assert inv != null;
        this.inv = inv;
        this.requires = TB.tt();
        this.assignable = TB.func(services.getTypeConverter().getLocSetLDT().getAllLocs());
        this.ensures = inv.getOriginalInv();
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
        return false;
    }

    @Override
    public String proofToString(Services services) {
        return null;
    }

    @Override
    public Contract setID(int newId) {
        return this;
    }

    @Override
    public String getTypeName() {
        return "Well-Definedness of " + inv.getDisplayName();
    }

    @Override
    public String getName() {
        return inv.getName();
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

    public ImmutableSet<Taclet> getTaclets(Services services) {
        ImmutableSet<Taclet> result = DefaultImmutableSet.<Taclet>nil();

        for (int i = 0; i < 2; i++) {
            TacletGenerator TG = TacletGenerator.getInstance();
            Name name = MiscTools.toValidTacletName("wd invariant "
                                                    + (getTarget().isStatic()? "static ": "")
                                                    + getTarget().name().toString()
                                                    + (i == 0 ? "" : " EQ"));

            //create schema variables
            final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
            final List<SchemaVariable> heapSVs = new LinkedList<SchemaVariable>();
            for(int j=0; j<HeapContext.getModHeaps(services, false).size(); j++) {
                heapSVs.add(SchemaVariableFactory.createTermSV(new Name("h"+j),
                                                       heapLDT.targetSort(),
                                                       false,
                                                       false));
            }
            final SchemaVariable selfSV =
                    getTarget().isStatic() ? null
                            : SchemaVariableFactory.createTermSV(new Name("self"),
                                                         inv.getKJT().getSort());
            final SchemaVariable eqSV = getTarget().isStatic()
                                        ? null
                                        : SchemaVariableFactory.createTermSV(
                    new Name("EQ"),
                    services.getJavaInfo().objectSort());

            ImmutableSet<Taclet> taclets =
                    TG.generateWdInvTaclet(name,
                                           heapSVs,
                                           selfSV,
                                           eqSV,
                                           inv.getInv(selfSV, services),
                                           getRequires(),
                                           getEnsures(),
                                           inv.getKJT(),
                                           getTarget().isStatic(),
                                           i == 1,
                                           services);
            result = result.union(taclets);

            //EQ taclet only for non-static invariants
            if (getTarget().isStatic()) {
                break;
            }
        }

        //return
        return result;
    }
}