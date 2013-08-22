package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.rule.Taclet;

public final class MethodWellDefinedness extends WellDefinednessCheck {
    /* breaks-clause, callable-clause, captures-clause,
     * choice-statement, continues-clause, diverges-clause, duration-clause, if-statement,
     * measured-clause, returns-clause, when-clause, working-space-clause,
     * initially-clause, constraint, signals-clause */
    private final Contract contract;

    private final Term forall;
    private final Term old;
    private final Term when;
    private final Term workingSpace;
    private final Term duration;
    private final Term globalDefs;
    private final boolean model;

    private MethodWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                  LocationVariable heap, OriginalVariables origVars,
                                  Precondition requires, Term assignable, Term accessible,
                                  Term ensures, Term mby, Term rep, Contract contract,
                                  Term forall, Term old, Term when, Term workingSpace,
                                  Term duration, Term globalDefs, boolean model) {
        super(name, id, type, target, heap, origVars, requires,
              assignable, accessible, ensures, mby, rep);
        this.contract = contract;
        this.forall = forall;
        this.old = old;
        this.when = when;
        this.workingSpace = workingSpace;
        this.duration = duration;
        this.globalDefs = globalDefs;
        this.model = model;
    }

    public MethodWellDefinedness(FunctionalOperationContract contract, Services services) {
        super(contract.getTypeName(), contract.id(), contract.getTarget(),
              contract.getOrigVars(), Type.OPERATION_CONTRACT, services);
        assert contract != null;
        this.contract = contract;
        this.model = false;
        final LocationVariable h = getHeap();
        final LocationVariable hPre = (LocationVariable) contract.getOrigVars().atPres.get(h);

        setRequires(contract.getRequires(h));
        setAssignable(contract.getAssignable(h));
        setAccessible(contract.getAccessible(h),
                      hPre != null ? contract.getAccessible(hPre) : null,
                      services);
        setEnsures(contract.getEnsures(h));
        setMby(contract.getMby());
        this.globalDefs = contract.getGlobalDefs();

        this.forall = TB.tt(); // TODO: Where do we get the forall-clause from?
        this.old = TB.tt(); // TODO: Where do we get the old-clause from?
        this.when = TB.tt(); // TODO: Where do we get the when-clause from?
        this.workingSpace = TB.tt(); // TODO: Where do we get the working_space-clause from?
        this.duration = TB.tt(); // TODO: Where do we get the duration-clause from?
    }

    public MethodWellDefinedness(DependencyContract contract, Services services) {
        super(contract.getTypeName(), contract.id(), contract.getTarget(),
              contract.getOrigVars(), Type.OPERATION_CONTRACT, services);
        assert contract != null;
        this.contract = contract;
        this.model = true;
        final LocationVariable h = getHeap();
        final LocationVariable hPre = (LocationVariable) contract.getOrigVars().atPres.get(h);

        setRequires(contract.getRequires(h));
        setAssignable(TB.allLocs(services));
        setAccessible(contract.getAccessible(h),
                      hPre != null ? contract.getAccessible(hPre) : null,
                      services);
        setEnsures(TB.tt());
        setMby(contract.getMby());
        this.globalDefs = contract.getGlobalDefs();

        this.forall = TB.tt(); // TODO: Where do we get the forall-clause from?
        this.old = TB.tt(); // TODO: Where do we get the old-clause from?
        this.when = TB.tt(); // TODO: Where do we get the when-clause from?
        this.workingSpace = TB.tt(); // TODO: Where do we get the working_space-clause from?
        this.duration = TB.tt(); // TODO: Where do we get the duration-clause from?
    }

    //-------------------------------------------------------------------------
    // Internal Methods
    //-------------------------------------------------------------------------

    private static Term[] getArgs(SchemaVariable sv, ParsableVariable heap,
                                  boolean isStatic,
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

    private void setAccessible(Term acc, Term accPre, Services services) {
        if (acc == null && accPre == null) {
            setAccessible(null);
        } else if (accPre == null) {
            setAccessible(acc);
        } else if (acc == null) {
            setAccessible(accPre);
        } else {
            setAccessible(TB.union(services, acc, accPre));
        }
    }

    @Override
    TermAndFunc generateMbyAtPreDef(ParsableVariable self,
                                    ImmutableList<ParsableVariable> params,
                                    Services services) {
        if (hasMby()) {
            final Function mbyAtPreFunc =
                    new Function(new Name(TB.newName(services, "mbyAtPre")),
                                 services.getTypeConverter().getIntegerLDT().targetSort());
            OriginalVariables origVars = getOrigVars();
            final Term mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby;
            if (params != null && self != null && !params.isEmpty()
                    && (params.iterator().next() instanceof ProgramVariable)
                    && (self instanceof ProgramVariable)) {
                ImmutableList<ProgramVariable> parameters =
                        ImmutableSLList.<ProgramVariable>nil();
                for (ParsableVariable pv: params) {
                    parameters = parameters.append((ProgramVariable)pv);
                }
                mby = contract.getMby((ProgramVariable)self, parameters, services);
            } else {
                mby = contract.getMby(origVars.self, origVars.params, services);
            }
            final Term mbyAtPreDef = TB.equals(mbyAtPre, mby);
            return new TermAndFunc(mbyAtPreDef, mbyAtPreFunc);
        } else {
            return new TermAndFunc(TB.tt(), null);
        }
    }

    ImmutableList<Term> getRest() {
        ImmutableList<Term> rest = super.getRest();
        final Term globalDefs = getGlobalDefs();
        if (globalDefs != null) {
            rest = rest.append(globalDefs);
        }
        return rest;
    }

    //-------------------------------------------------------------------------
    // Public Interface
    //-------------------------------------------------------------------------

    public Contract getMethodContract() {
        return this.contract;
    }

    @Override
    public boolean isModel() {
        return this.model;
    }

    public Term getForall() {
        return this.forall;
    }

    public Term getOld() {
        return this.old;
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

    public Taclet createOperationTaclet(Services services) {
        final boolean isStatic = getTarget().isStatic();
        final LocationVariable heap = getHeap();
        final SchemaVariable heapSV =
                SchemaVariableFactory.createTermSV(heap.name(), heap.sort());
        final SchemaVariable selfSV =
                SchemaVariableFactory.createTermSV(new Name("callee"), getKJT().getSort());
        final ImmutableList<ParsableVariable> paramsSV = paramsSV();

        final Term pre = getPre(replaceSV(getRequires(), selfSV, paramsSV),
                                selfSV, heapSV, paramsSV, services).term;
        final Term[] args = getArgs(selfSV, heapSV, isStatic, paramsSV);
        final Term wdArgs = TB.and(TB.wd(args, services));
        return createTaclet(OP_PREFIX, TB.var(selfSV), TB.func(getTarget(), args),
                            TB.and(wdArgs, pre), services);
    }

    @Override
    public Term getGlobalDefs() {
        return this.globalDefs;
    }

    @Override
    public boolean transactionApplicableContract() {
        return contract.transactionApplicableContract();
    }

    @Override
    public MethodWellDefinedness setID(int newId) {
        return new MethodWellDefinedness(getName(),
                                         newId,
                                         type(),
                                         getTarget(),
                                         getHeap(),
                                         getOrigVars(),
                                         getRequires(),
                                         getAssignable(),
                                         getAccessible(),
                                         getEnsures(),
                                         getMby(),
                                         getRepresents(),
                                         contract,
                                         forall,
                                         old,
                                         when,
                                         workingSpace,
                                         duration,
                                         globalDefs,
                                         isModel());
    }

    @Override
    public MethodWellDefinedness setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new MethodWellDefinedness(getName(),
                                         id(),
                                         type(),
                                         newPM,
                                         getHeap(),
                                         getOrigVars(),
                                         getRequires(),
                                         getAssignable(),
                                         getAccessible(),
                                         getEnsures(),
                                         getMby(),
                                         getRepresents(),
                                         contract.setTarget(newKJT, newPM),
                                         forall,
                                         old,
                                         when,
                                         workingSpace,
                                         duration,
                                         globalDefs,
                                         isModel());
    }

    @Override
    public String getTypeName() {
        return "Well-Definedness of " + (isModel() ? "model " : "") + contract.getTypeName();
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