package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.rule.Taclet;

public final class MethodWellDefinedness extends WellDefinednessCheck {
    /* accessible-clause, assignable-clause, breaks-clause, callable-clause, captures-clause,
     * choice-statement, continues-clause, diverges-clause, duration-clause, if-statement,
     * measured-clause, returns-clause, when-clause, working-space-clause, requires-clause,
     * initially-clause, constraint, ensures-clause, signals-clause */
    private final FunctionalOperationContract contract;

    private Term forall;
    private Term old;
    private Term diverges = TB.ff();
    private Term when;
    private Term workingSpace;
    private Term duration;
    private Term signalsOnly;
    private Term signals = TB.ff();

    private MethodWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                  LocationVariable heap, Precondition requires,
                                  Term assignable, Term ensures,
                                  FunctionalOperationContract contract, Term forall,
                                  Term old, Term diverges, Term when, Term workingSpace,
                                  Term duration, Term signalsOnly, Term signals) {
        super(name, id, type, target, heap, requires, assignable, ensures);
        this.contract = contract;
        this.forall = forall;
        this.old = old;
        this.diverges = diverges;
        this.when = when;
        this.workingSpace = workingSpace;
        this.duration = duration;
        this.signalsOnly = signalsOnly;
        this.signals = signals;
    }

    public MethodWellDefinedness(FunctionalOperationContract contract, Services services) {
        super(contract.getTypeName(), contract.id(), contract.getTarget(),
              Type.OPERATION_CONTRACT, services);
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

    //-------------------------------------------------------------------------
    // Internal Methods
    //-------------------------------------------------------------------------

    private static Term[] getArgs(SchemaVariable sv, LocationVariable heap, boolean isStatic,
                                  ImmutableList<ParsableVariable> params) {
        Term[] args = new Term[params.size() + (isStatic ? 1 : 2)];
        int i = 0;
        args[i++] = TB.var(heap);
        if (!isStatic) {
            args[i++] = TB.var(sv);
        }
        for (ParsableVariable arg : params) {
            assert arg instanceof SchemaVariable;
            args[i++] = TB.var(arg);
        }
        return args;
    }

    private ImmutableList<ParsableVariable> paramsSV() {
        ImmutableList<ParsableVariable> paramsSV =
                ImmutableSLList.<ParsableVariable>nil();
        for (ProgramVariable pv: getOrigVars().params) {
            paramsSV = paramsSV.append(SchemaVariableFactory.createTermSV(
                    pv.name(), pv.getKeYJavaType().getSort()));
        }
        return paramsSV;
    }

    //-------------------------------------------------------------------------
    // Public Interface
    //-------------------------------------------------------------------------

    public FunctionalOperationContract getOperationContract() {
        return this.contract;
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

    public Taclet createOperationTaclet(Services services) {
        final boolean isStatic = getTarget().isStatic();
        final LocationVariable heap = getHeap();
        final SchemaVariable sv =
                SchemaVariableFactory.createTermSV(new Name("callee"), getKJT().getSort());
        final ImmutableList<ParsableVariable> paramsSV = paramsSV();
        final Term pre = getPre(replaceSV(getRequires(), sv, paramsSV),
                                sv, heap, paramsSV, services).term;
        final Term[] args = getArgs(sv, heap, isStatic, paramsSV);
        final Term wdArgs = TB.and(TB.wd(args, services));
        return createTaclet(OP_PREFIX, TB.var(sv), heap, TB.func(getTarget(), args),
                            TB.and(wdArgs, pre), services);
    }

    @Override
    public boolean transactionApplicableContract() {
        return contract.transactionApplicableContract();
    }

    @Override
    public Contract setID(int newId) {
        return new MethodWellDefinedness(getName(),
                                         newId,
                                         type(),
                                         getTarget(),
                                         getHeap(),
                                         getRequires(),
                                         getAssignable(),
                                         getEnsures(),
                                         contract,
                                         forall,
                                         old,
                                         diverges,
                                         when,
                                         workingSpace,
                                         duration,
                                         signalsOnly,
                                         signals);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new MethodWellDefinedness(getName(),
                                         id(),
                                         type(),
                                         newPM,
                                         getHeap(),
                                         getRequires(),
                                         getAssignable(),
                                         getEnsures(),
                                         (FunctionalOperationContract)
                                             contract.setTarget(newKJT, newPM),
                                         forall,
                                         old,
                                         diverges,
                                         when,
                                         workingSpace,
                                         duration,
                                         signalsOnly,
                                         signals);
    }

    @Override
    public String getTypeName() {
        return "Well-Definedness of " + contract.getTypeName();
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
    public POTerms createPOTerms() {
        final Precondition pre = this.getRequires();
        final Term mod = this.getAssignable();
        final ImmutableList<Term> rest = ImmutableSLList.<Term>nil();
        final Term post = this.getEnsures();
        return new POTerms(pre, mod, rest, post);
    }

    @Override
    public OriginalVariables getOrigVars() {
        assert getOperationContract() != null;
        return getOperationContract().getOrigVars();
    }
}