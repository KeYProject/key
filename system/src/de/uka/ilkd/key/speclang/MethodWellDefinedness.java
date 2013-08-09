package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

public final class MethodWellDefinedness extends WellDefinednessCheck {
    /* accessible-clause, assignable-clause, breaks-clause, callable-clause, captures-clause,
     * choice-statement, continues-clause, diverges-clause, duration-clause, if-statement,
     * measured-clause, returns-clause, when-clause, working-space-clause, requires-clause,
     * initially-clause, constraint, ensures-clause, signals-clause */
    private final FunctionalOperationContract contract;

    Term forall;
    Term old;
    Term diverges = TB.ff();
    Term when;
    Term workingSpace;
    Term duration;
    Term signalsOnly;
    Term signals = TB.ff();

    public MethodWellDefinedness(FunctionalOperationContract contract, Services services) {
        super(contract.getTarget(), Type.METHOD_CONTRACT, services);
        assert contract != null;
        this.contract = contract;
        LocationVariable h = getHeap();

        this.setRequires(contract.getRequires(h));
        this.setAssignable(contract.getAssignable(h));
        this.setEnsures(contract.getEnsures(h));

        this.forall = TB.tt(); // TODO: Where do we get the forall-clause from?
        this.old = TB.tt(); // TODO: Where do we get the old-clause from?
        this.diverges = TB.tt(); // TODO: Where do we get the diverges-clause from?
        this.when = TB.tt(); // TODO: Where do we get the when-clause from?
        this.workingSpace = TB.tt(); // TODO: Where do we get the working_space-clause from?
        this.duration = TB.tt(); // TODO: Where do we get the duration-clause from?
        this.signalsOnly = TB.tt(); // TODO: Where do we get the signal_only-clause from?
        this.signals = TB.tt(); // TODO: Where do we get the signals-clause from?
    }

    public FunctionalOperationContract getContract() {
        return this.contract;
    }

    // TODO: Not used atm, do we even need this method here? Better alternatives?
    public Term getPre(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
        return contract.getPre(getHeap(), selfVar, paramVars, atPreVars, services);
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

    @Override
    public Triple<Pair<Term, Term>, ImmutableList<Term>, Term> createPOTerm() {
        Pair<Term, Term> pre = this.getRequires();
        ImmutableList<Term> c = ImmutableSLList.<Term>nil();
        c = c.append(this.getAssignable());
        Term post = this.getEnsures();
        return new Triple<Pair<Term, Term>, ImmutableList<Term>, Term>(pre, c, post);
    }

    @Override
    public OriginalVariables getOrigVars() {
        assert getContract() != null;
        return getContract().getOrigVars();
    }
}