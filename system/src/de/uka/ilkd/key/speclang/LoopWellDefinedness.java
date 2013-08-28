package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;

public class LoopWellDefinedness extends WellDefinednessCheck {

    private final LoopInvariant inv;

    private LoopWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                LocationVariable heap, OriginalVariables origVars,
                                Condition requires, Term assignable, Term accessible,
                                Condition ensures, Term mby, Term rep, LoopInvariant inv) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
        this.inv = inv;
    }

    public LoopWellDefinedness(LoopInvariant inv, Services services) {
        super(ContractFactory.generateContractTypeName(inv.getName(),
                                                       inv.getKJT(),
                                                       inv.getTarget(),
                                                       inv.getKJT()),
              inv.getLoop().getStartPosition().getLine(), inv.getTarget(), inv.getOrigVars(),
              Type.LOOP_INVARIANT, services);
        assert inv != null;
        final LocationVariable h = getHeap();
        this.inv = inv;
        setMby(inv.getInternalVariant());
        setRequires(inv.getInternalInvariants().get(h));
        setAssignable(inv.getInternalModifies().get(h), services);
        setEnsures(inv.getInternalInvariants().get(h));
    }

    @Override
    TermAndFunc generateMbyAtPreDef(ParsableVariable self,
            ImmutableList<ParsableVariable> params, Services services) {
        return new TermAndFunc(TB.tt(), null);
    }

    @Override
    ImmutableList<Term> getRest() {
        return super.getRest();
    }

    public LoopInvariant getInvariant() {
        return this.inv;
    }

    @Override
    public String getBehaviour() {
        return "";
    }

    @Override
    public Term getGlobalDefs() {
        throw new UnsupportedOperationException("Not applicable for well-definedness of loops.");
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
                                       getRepresents(), getInvariant());
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new LoopWellDefinedness(getName(), id(), type(), newPM, getHeap(),
                                       getOrigVars(), getRequires(), getAssignable(),
                                       getAccessible(), getEnsures(), getMby(),
                                       getRepresents(), getInvariant().setTarget(newKJT, newPM));
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
    public boolean isModel() {
        return false;
    }
}