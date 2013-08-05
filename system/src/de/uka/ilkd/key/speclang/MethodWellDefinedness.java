package de.uka.ilkd.key.speclang;

import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.AutoSpecTermLabel;
import de.uka.ilkd.key.logic.ShortcutEvaluationTermLabel;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

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

    public MethodWellDefinedness(FunctionalOperationContract contract, Services services) {
        super(contract.getTarget(), Type.METHOD_CONTRACT, services);
        assert contract != null;
        this.contract = contract;

        this.requires = order(contract.getRequires(heap));
        this.assignable = contract.getAssignable(heap);
        this.ensures = contract.getEnsures(heap);

        this.forall = TB.tt(); // TODO: Where do we get the forall-clause from?
        this.old = TB.tt(); // TODO: Where do we get the old-clause from?
        this.diverges = TB.tt(); // TODO: Where do we get the diverges-clause from?
        this.when = TB.tt(); // TODO: Where do we get the when-clause from?
        this.workingSpace = TB.tt(); // TODO: Where do we get the working_space-clause from?
        this.duration = TB.tt(); // TODO: Where do we get the duration-clause from?
        this.signalsOnly = TB.tt(); // TODO: Where do we get the signal_only-clause from?
        this.signals = TB.tt(); // TODO: Where do we get the signals-clause from?
    }

    // TODO: Not used atm, do we even need this method here? Better alternatives?
    public Term getPre(ProgramVariable selfVar,
                       ImmutableList<ProgramVariable> paramVars,
                       Map<LocationVariable, ? extends ProgramVariable> atPreVars,
                       Services services) {
        return contract.getPre(heap, selfVar, paramVars, atPreVars, services);
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

    @Override
    public Triple<Term, ImmutableList<Term>, Term> createPOTerm() {
        Term pre = this.getRequires();
        ImmutableList<Term> c = ImmutableSLList.<Term>nil();
        c = c.append(this.getAssignable());
        Term post = this.getEnsures();
        return new Triple<Term, ImmutableList<Term>, Term>(pre, c, post);
    }

    private static Term order(Term spec) {
        Pair<ImmutableList<Term>, ImmutableList<Term>> p = suborder(spec);
        ImmutableList<Term> start = p.first;
        ImmutableList<Term> end   = p.second;
        Term s = TB.and(start);
        Term e = TB.and(end);
        return TB.label(TB.and(s, e), ShortcutEvaluationTermLabel.INSTANCE);
    }

    private static Pair<ImmutableList<Term>, ImmutableList<Term>> suborder(Term spec) {
        assert spec != null;
        ImmutableList<Term> start = ImmutableSLList.<Term>nil();
        ImmutableList<Term> end = ImmutableSLList.<Term>nil();
        if(spec.arity() > 0
                && spec.op().equals(Junctor.AND)) {
            for (Term sub: spec.subs()) {
                if(sub.hasLabels()
                        && sub.getLabels().contains(AutoSpecTermLabel.INSTANCE)) {
                    sub = relabel(sub);
                    Pair<ImmutableList<Term>, ImmutableList<Term>> p = suborder(sub);
                    start = start.append(p.first).append(p.second);
                } else {
                    Pair<ImmutableList<Term>, ImmutableList<Term>> p = suborder(sub);
                    start = start.append(p.first);
                    end = end.append(p.second);
                }
            }
            return new Pair<ImmutableList<Term>, ImmutableList<Term>> (start, end);
        } else {
            end = end.append(spec);
            return new Pair<ImmutableList<Term>, ImmutableList<Term>> (start, end);
        }
    }
}