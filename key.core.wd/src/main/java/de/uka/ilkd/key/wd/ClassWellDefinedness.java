/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.wd;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.speclang.ClassInvariant;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

/**
 * A contract for checking the well-definedness of a specification for a class invariant.
 *
 * @author Michael Kirsten
 */
public final class ClassWellDefinedness extends WellDefinednessCheck {

    private final ClassInvariant inv;

    private ClassWellDefinedness(String name, int id, Type type, IObserverFunction target,
            LocationVariable heap, OriginalVariables origVars, Condition requires, JTerm modifiable,
            JTerm accessible, Condition ensures, JTerm mby, JTerm rep, ClassInvariant inv,
            TermBuilder tb) {
        super(name, id, type, target, heap, origVars, requires, modifiable, accessible, ensures,
            mby, rep, tb);
        this.inv = inv;
    }

    public ClassWellDefinedness(ClassInvariant inv, IObserverFunction target, JTerm accessible,
            JTerm mby, Services services) {
        super(inv.getKJT().getFullName() + "." + "JML class invariant", 0, target,
            inv.getOrigVars(), Type.CLASS_INVARIANT, services);
        assert inv != null;
        this.inv = inv;
        setRequires(inv.getOriginalInv());
        setModifiable(TB.strictlyNothing(), services);
        setEnsures(inv.getOriginalInv());
        setAccessible(accessible);
        setMby(mby);
    }

    @Override
    public ClassWellDefinedness map(UnaryOperator<JTerm> op, Services services) {
        return new ClassWellDefinedness(getName(), id(), type(), getTarget(), getHeap(),
            getOrigVars(), getRequires().map(op), op.apply(getModifiable()),
            op.apply(getAccessible()), getEnsures().map(op), op.apply(getMby()),
            op.apply(getRepresents()), inv.map(op, services), services.getTermBuilder());
    }

    @Override
    Function generateMbyAtPreFunc(Services services) {
        return null;
    }

    @Override
    ImmutableList<JTerm> getRest() {
        return super.getRest();
    }

    /**
     * Creates a well-definedness taclet for an invariant reference. Actually we should be able to
     * statically denote this taclet in the rule folder, but somehow the type java.lang.Object is
     * not available there in the required manner.
     *
     * @param services
     * @return the well-definedness taclet for an invariant reference
     */
    public static ImmutableSet<RewriteTaclet> createInvTaclet(Services services) {
        final TermBuilder TB = services.getTermBuilder();
        final KeYJavaType kjt = services.getJavaInfo().getJavaLangObject();
        final String prefix = INV_TACLET;
        final LocationVariable heap = services.getTypeConverter().getHeapLDT().getHeap();
        final TermSV heapSV =
            SchemaVariableFactory.createTermSV(new Name("h"), heap.sort());
        final TermSV sv = SchemaVariableFactory.createTermSV(new Name("a"), kjt.getSort());
        final JTerm var = TB.var(sv);
        final JTerm wdSelf = TB.wd(var);
        final JTerm[] heaps = { TB.var(heapSV) };
        final JTerm staticInvTerm = TB.staticInv(heaps, kjt);
        final JTerm invTerm = TB.inv(heaps, var);
        final JTerm wdHeaps = TB.and(TB.wd(heaps));
        final JTerm wellFormed = TB.wellFormed(TB.var(heapSV));
        final JTerm pre = TB.and(wdSelf, wdHeaps, wellFormed);
        final JTerm staticPre = TB.and(wdHeaps, wellFormed);
        final RewriteTaclet inv =
            createTaclet(prefix, var, invTerm, pre, false, services);
        final RewriteTaclet staticInv = createTaclet(prefix + "_Static", var,
            staticInvTerm, staticPre, true, services);
        return DefaultImmutableSet.<RewriteTaclet>nil().add(inv).add(staticInv);
    }

    public ClassInvariant getInvariant() {
        return this.inv;
    }

    public void addInv(JTerm inv) {
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
        final ClassWellDefinedness cwd = (ClassWellDefinedness) wdc;
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
            getOrigVars(), getRequires(), getModifiable(), getAccessible(), getEnsures(), getMby(),
            getRepresents(), getInvariant(), TB);
    }

    @Override
    public ClassWellDefinedness setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new ClassWellDefinedness(getName(), id(), type(), newPM, getHeap(), getOrigVars(),
            getRequires(), getModifiable(), getAccessible(), getEnsures(), getMby(),
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
    public JTerm getGlobalDefs() {
        return null;
    }

    @Override
    public JTerm getAxiom() {
        return null;
    }
}
