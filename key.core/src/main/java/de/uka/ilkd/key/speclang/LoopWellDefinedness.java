/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;

import org.key_project.util.collection.ImmutableSet;

/**
 * A contract for checking the well-definedness of a jml loop invariant.
 *
 * @author Michael Kirsten
 */
public class LoopWellDefinedness extends StatementWellDefinedness {

    private final LoopSpecification inv;

    private LoopWellDefinedness(String name, int id, Type type, IObserverFunction target,
            LocationVariable heap, OriginalVariables origVars, Condition requires, Term assignable,
            Term accessible, Condition ensures, Term mby, Term rep, LoopSpecification inv,
            TermBuilder tb) {
        super(name, id, type, target, heap, origVars, requires, assignable, accessible, ensures,
            mby, rep, tb);
        this.inv = inv;
    }

    public LoopWellDefinedness(LoopSpecification inv, ImmutableSet<ProgramVariable> params,
            Services services) {
        super(inv.getName(), inv.getLoop().getStartPosition().line(), inv.getTarget(),
            inv.getOrigVars().add(convertParams(params)), Type.LOOP_INVARIANT, services);
        assert inv != null;
        final LocationVariable h = getHeap();
        this.inv = inv;
        setMby(inv.getInternalVariant());
        setRequires(inv.getInternalInvariants().get(h));
        setAssignable(inv.getInternalModifies().get(h), services);
        setEnsures(inv.getInternalInvariants().get(h));
    }

    @Override
    SequentFormula generateSequent(SequentTerms seq, TermServices services) {
        // wd(phi) & (phi & wf(anon) -> wd(mod) & wd(variant) & {anon^mod}(wd(phi) & wd(variant)))
        final Term imp =
            TB.imp(TB.and(seq.pre, seq.wfAnon), TB.and(seq.wdMod, seq.wdRest, seq.anonWdPost));
        final Term wdPre = TB.wd(seq.pre);
        return new SequentFormula(TB.apply(seq.context, TB.and(wdPre, imp)));
    }

    @Override
    public LoopSpecification getStatement() {
        return this.inv;
    }

    @Override
    public LoopWellDefinedness map(UnaryOperator<Term> op, Services services) {
        return new LoopWellDefinedness(getName(), id(), type(), getTarget(), getHeap(),
            getOrigVars(), getRequires().map(op), op.apply(getAssignable()),
            op.apply(getAccessible()), getEnsures().map(op), op.apply(getMby()),
            op.apply(getRepresents()), inv.map(op, services), services.getTermBuilder());
    }

    @Override
    public boolean transactionApplicableContract() {
        return false;
    }

    @Override
    public Contract setID(int newId) {
        return new LoopWellDefinedness(getName(), newId, type(), getTarget(), getHeap(),
            getOrigVars(), getRequires(), getAssignable(), getAccessible(), getEnsures(), getMby(),
            getRepresents(), getStatement(), TB);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new LoopWellDefinedness(getName(), id(), type(), newPM, getHeap(), getOrigVars(),
            getRequires(), getAssignable(), getAccessible(), getEnsures(), getMby(),
            getRepresents(), getStatement().setTarget(newKJT, newPM), TB);
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
    public LoopWellDefinedness combine(WellDefinednessCheck wdc, TermServices services) {
        assert wdc instanceof LoopWellDefinedness;
        final LoopWellDefinedness lwd = (LoopWellDefinedness) wdc;
        assert this.getStatement().getName().equals(lwd.getStatement().getName());
        assert this.getStatement().getLoop().getStartPosition().line() == lwd.getStatement()
                .getLoop().getStartPosition().line();
        assert this.getStatement().getTarget().equals(lwd.getStatement().getTarget());
        assert this.getStatement().getKJT().equals(lwd.getStatement().getKJT());

        super.combine(lwd, services);
        return this;
    }
}
