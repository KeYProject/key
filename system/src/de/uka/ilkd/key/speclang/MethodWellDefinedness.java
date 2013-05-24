package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.pp.LogicPrinter;

public final class MethodWellDefinedness extends WellDefinednessCheck {
    /* accessible-clause, assignable-clause, breaks-clause, callable-clause, captures-clause,
     * choice-statement, continues-clause, diverges-clause, duration-clause, if-statement,
     * measured-clause, returns-clause, when-clause, working-space-clause, requires-clause,
     * initially-clause, constraint, ensures-clause, signals-clause */
    final Contract contract;

    Term forall;
    Term old;
    Term diverges = TB.ff();
    Term when;
    Term workingSpace;
    Term duration;
    Term ensures = TB.tt();
    Term signalsOnly;
    Term signals = TB.ff();

    public MethodWellDefinedness(Contract contract, Services services) {
        super(contract.getTarget(), Type.METHOD_CONTRACT);
        assert contract != null;
        this.contract = contract;
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final LocationVariable baseHeap = heapLDT.getHeap();
        this.requires = contract.getRequires(baseHeap);
        this.assignable = contract.getAssignable(baseHeap);

        this.forall = TB.tt(); // TODO: Where do we get the forall-clause from?
        this.old = TB.tt(); // TODO: Where do we get the old-clause from?
        this.diverges = TB.tt(); // TODO: Where do we get the diverges-clause from?
        this.when = TB.tt(); // TODO: Where do we get the when-clause from?
        this.workingSpace = TB.tt(); // TODO: Where do we get the working_space-clause from?
        this.duration = TB.tt(); // TODO: Where do we get the duration-clause from?
        this.ensures = TB.tt(); // TODO: Where do we get the ensures-clause from?
        this.signalsOnly = TB.tt(); // TODO: Where do we get the signal_only-clause from?
        this.signals = TB.tt(); // TODO: Where do we get the signals-clause from?
    }

    public Term getForall() {
        return this.forall;
    }

    public Term getOld() {
        return this.old;
    }

    public Term getDiverges() {
        return this.diverges;
    }

    public Term getWhen() {
        return this.when;
    }

    public Term getWorkingSpace() {
        return this.workingSpace;
    }

    public Term getDuration() {
        return this.duration;
    }

    public Term getEnsures() {
        return this.ensures;
    }

    public Term getSignalsOnly() {
        return this.signalsOnly;
    }

    public Term getSignals() {
        return this.signals;
    }

    @Override
    public Type type() {
        return Type.METHOD_CONTRACT;
    }

    @Override
    public int id() {
        return contract.id();
    }

    @Override
    public boolean transactionApplicableContract() {
        return contract.transactionApplicableContract();
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
        return "Well-Definedness of " + contract.getTypeName();
    }

    @Override
    public String getName() {
        return "Well-Definedness of " + contract.getName();
    }

    @Override
    public VisibilityModifier getVisibility() {
        return contract.getVisibility();
    }

    @Override
    public KeYJavaType getKJT() {
        return contract.getKJT();
    }

}
