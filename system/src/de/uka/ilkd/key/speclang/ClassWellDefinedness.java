// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.rule.Taclet;

/**
 * A contract for checking the well-definedness of a specification for a class invariant.
 *
 * @author Michael Kirsten
 */
public final class ClassWellDefinedness extends WellDefinednessCheck {

    private final ClassInvariant inv;

    private ClassWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                 LocationVariable heap, OriginalVariables origVars,
                                 Condition requires, Term assignable, Term accessible,
                                 Condition ensures, Term mby, Term rep, ClassInvariant inv) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
        this.inv = inv;
    }

    public ClassWellDefinedness(ClassInvariant inv, IObserverFunction target,
                                Term accessible, Term mby, Services services) {
        super("JML class invariant in " + inv.getKJT().getName(), 0, target, inv.getOrigVars(),
              Type.CLASS_INVARIANT, services);
        assert inv != null;
        this.inv = inv;
        setRequires(TB.tt());
        setAssignable(TB.empty(services), services);
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

    public static ImmutableSet<Taclet> createInvTaclet(KeYJavaType kjt, Services services) {
        final String prefix = WellDefinednessCheck.INV_TACLET;
        final LocationVariable heap = services.getTypeConverter().getHeapLDT().getHeap();
        final SchemaVariable heapSV =
                SchemaVariableFactory.createTermSV(heap.name(), heap.sort());
        final SchemaVariable sv =
                SchemaVariableFactory.createTermSV(new Name("self"), kjt.getSort());
        final Term var = TB.var(sv);
        final Term wdSelf = TB.wd(var, services);
        final Term[] heaps = new Term[] {TB.var(heapSV)};
        final Term staticInvTerm = TB.staticInv(services, heaps, kjt);
        final Term invTerm = TB.inv(services, heaps, var);
        final Term wdHeaps = TB.and(TB.wd(heaps, services));
        final Term wellFormed = TB.wellFormed(TB.var(heapSV), services);
        final Term pre = TB.and(wdSelf, wdHeaps, wellFormed);
        final Term staticPre = TB.and(wdHeaps, wellFormed);
        final Taclet inv =
                WellDefinednessCheck.createTaclet(prefix + kjt.getName(),
                                                  var, invTerm, pre, false, services);
        final Taclet staticInv =
                WellDefinednessCheck.createTaclet(prefix + "Static_" + kjt.getName(),
                                                  var, staticInvTerm, staticPre, true, services);
        return DefaultImmutableSet.<Taclet>nil().add(inv).add(staticInv);
    }

    public ClassInvariant getInvariant() {
        return this.inv;
    }

    public void addInv(Term inv) {
        addEnsures(inv);
    }

    @Override
    public String getBehaviour() {
        return "";
    }

    @Override
    public boolean isModel() {
        return false;
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
                                        getRepresents(), getInvariant());
    }

    @Override
    public ClassWellDefinedness setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new ClassWellDefinedness(getName(), id(), type(), newPM, getHeap(),
                                        getOrigVars(), getRequires(), getAssignable(),
                                        getAccessible(), getEnsures(), getMby(),
                                        getRepresents(), getInvariant().setKJT(newKJT));
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
    public Term getGlobalDefs() {
        throw new UnsupportedOperationException("Not applicable for well-definedness of invariants.");
    }
}