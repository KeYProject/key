// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
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
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.rule.RewriteTaclet;

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
                                 Condition ensures, Term mby, Term rep, ClassInvariant inv,
                                 TermBuilder tb) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep, tb);
        this.inv = inv;
    }

    public ClassWellDefinedness(ClassInvariant inv, IObserverFunction target,
                                Term accessible, Term mby, Services services) {
        super(inv.getKJT().getFullName() + "." + "JML class invariant", 0, target,
              inv.getOrigVars(), Type.CLASS_INVARIANT, services);
        assert inv != null;
        this.inv = inv;
        setRequires(inv.getOriginalInv());
        setAssignable(TB.strictlyNothing(), services);
        setEnsures(inv.getOriginalInv());
        setAccessible(accessible);
        setMby(mby);
    }

    @Override
    Function generateMbyAtPreFunc(Services services) {
        return null;
    }

    @Override
    ImmutableList<Term> getRest() {
        return super.getRest();
    }

    /**
     * Creates a well-definedness taclet for an invariant reference. Actually we should
     * be able to statically denote this taclet in the rule folder, but somehow the type
     * java.lang.Object is not available there in the required manner.
     * @param services
     * @return the well-definedness taclet for an invariant reference
     */
    public static ImmutableSet<RewriteTaclet> createInvTaclet(Services services) {
        final TermBuilder TB = services.getTermBuilder();
        final KeYJavaType kjt = services.getJavaInfo().getJavaLangObject();
        final String prefix = WellDefinednessCheck.INV_TACLET;
        final LocationVariable heap = services.getTypeConverter().getHeapLDT().getHeap();
        final SchemaVariable heapSV =
                SchemaVariableFactory.createTermSV(new Name("h"), heap.sort());
        final SchemaVariable sv =
                SchemaVariableFactory.createTermSV(new Name("a"), kjt.getSort());
        final Term var = TB.var(sv);
        final Term wdSelf = TB.wd(var);
        final Term[] heaps = new Term[] {TB.var(heapSV)};
        final Term staticInvTerm = TB.staticInv(heaps, kjt);
        final Term invTerm = TB.inv(heaps, var);
        final Term wdHeaps = TB.and(TB.wd(heaps));
        final Term wellFormed = TB.wellFormed(TB.var(heapSV));
        final Term pre = TB.and(wdSelf, wdHeaps, wellFormed);
        final Term staticPre = TB.and(wdHeaps, wellFormed);
        final RewriteTaclet inv =
                WellDefinednessCheck.createTaclet(prefix, var, invTerm, pre, false, services);
        final RewriteTaclet staticInv =
                WellDefinednessCheck.createTaclet(prefix + "_Static", var, staticInvTerm,
                                                  staticPre, true, services);
        return DefaultImmutableSet.<RewriteTaclet>nil().add(inv).add(staticInv);
    }

    public ClassInvariant getInvariant() {
        return this.inv;
    }

    public final void addInv(Term inv) {
        addRequires(inv);
        addEnsures(inv);
    }

    @Override
    public String getBehaviour() {
        return "";
    }

    @Override
    public boolean modelField() {
        return false;
    }

    @Override
    public ClassWellDefinedness combine(WellDefinednessCheck wdc, TermServices services) {
        assert wdc instanceof ClassWellDefinedness;
        final ClassWellDefinedness cwd = (ClassWellDefinedness)wdc;
        assert this.getInvariant().getKJT().equals(cwd.getInvariant().getKJT());
        super.combine(cwd, services);
        return this;
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
                                        getRepresents(), getInvariant(), TB);
    }

    @Override
    public ClassWellDefinedness setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new ClassWellDefinedness(getName(), id(), type(), newPM, getHeap(),
                                        getOrigVars(), getRequires(), getAssignable(),
                                        getAccessible(), getEnsures(), getMby(),
                                        getRepresents(), getInvariant().setKJT(newKJT), TB);
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
        return null;
    }

    @Override
    public Term getAxiom() {
        return null;
    }
}