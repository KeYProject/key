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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletGoalTemplate;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;

/**
 * A contract for checking the well-definedness of a specification for a method or model field.
 * Additionally to the general well-definedness contract, it consists of other definitions for
 * the contract.
 *
 * @author Michael Kirsten
 */
public final class MethodWellDefinedness extends WellDefinednessCheck {

    private final Contract contract;

    private Term globalDefs;
    private final boolean model;

    private MethodWellDefinedness(String name, int id, Type type, IObserverFunction target,
                                  LocationVariable heap, OriginalVariables origVars,
                                  Condition requires, Term assignable, Term accessible,
                                  Condition ensures, Term mby, Term rep, Contract contract,
                                  Term globalDefs, boolean model) {
        super(name, id, type, target, heap, origVars, requires, assignable, accessible,
              ensures, mby, rep);
        this.contract = contract;
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
        setAssignable(contract.hasModifiesClause(h) ? contract.getAssignable(h) : TB.strictlyNothing(),
                      services);
        combineAccessible(contract.getAccessible(h),
                      hPre != null ? contract.getAccessible(hPre) : null,
                      services);
        setEnsures(contract.getEnsures(h));
        setMby(contract.getMby());
        this.globalDefs = contract.getGlobalDefs();
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
        setAssignable(TB.strictlyNothing(), services);
        combineAccessible(contract.getAccessible(h),
                      hPre != null ? contract.getAccessible(hPre) : null,
                      services);
        setEnsures(TB.tt());
        setMby(contract.getMby());
        this.globalDefs = contract.getGlobalDefs();
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

    public RewriteTaclet createOperationTaclet(Services services) {
        final String prefix;
        final IObserverFunction target = getTarget();
        final String tName = target.name().toString();
        final boolean isStatic = target.isStatic();
        final LocationVariable heap = getHeap();
        final SchemaVariable heapSV =
                SchemaVariableFactory.createTermSV(heap.name(), heap.sort());
        final SchemaVariable selfSV =
                SchemaVariableFactory.createTermSV(new Name("callee"), getKJT().getSort());
        final ImmutableList<ParsableVariable> paramsSV = paramsSV();
        String ps = "";
        for (ParsableVariable pv: paramsSV) {
            ps = ps + " " + pv.sort();
        }
        final Term[] args = getArgs(selfSV, heapSV, isStatic, paramsSV);
        if (isNormal() /*&& isPure() TODO: Necessary?*/) {
            prefix = WellDefinednessCheck.OP_TACLET;
            final boolean isConstructor =
                    target instanceof IProgramMethod && ((IProgramMethod)target).isConstructor();
            final Term pre = getPre(replaceSV(getRequires(), selfSV, paramsSV),
                                    selfSV, heapSV, paramsSV, true, services).term;
            final Term wdArgs =
                    TB.and(TB.wd(getArgs(selfSV, heapSV, isStatic || isConstructor, paramsSV),
                                 services));
            return createTaclet(prefix + (isStatic ? " Static " : " ") + tName + ps,
                                TB.var(selfSV), TB.func(target, args),
                                TB.and(wdArgs, pre), isStatic || isConstructor, services);
        } else {
            prefix = WellDefinednessCheck.OP_EXC_TACLET;
            return createExcTaclet(prefix + (isStatic ? " Static " : " ") + tName + ps,
                                   TB.func(target, args), services);
        }
    }

    public RewriteTaclet combineTaclets(RewriteTaclet t1, RewriteTaclet t2, Services services) {
        assert t1.goalTemplates().size() == 1;
        assert t2.goalTemplates().size() == 1;
        final RewriteTacletGoalTemplate g1 = (RewriteTacletGoalTemplate)t1.goalTemplates().head();
        final RewriteTacletGoalTemplate g2 = (RewriteTacletGoalTemplate)t2.goalTemplates().head();
        return createTaclet(t1.name().toString(), t1.find(), t2.find(),
                            g1.replaceWith(), g2.replaceWith(), services);
    }

    @Override
    public String getBehaviour() {
        if (getMethodContract().getName().contains("normal_behavior")) {
            return "normal";
        } else if (getMethodContract().getName().contains("exceptional_behavior")) {
            return "exc";
        } else if (getMethodContract().getName().contains("model_behavior")) {
            return "model";
        } else if (getMethodContract().getName().contains("break_behavior")) {
            return "break";
        } else if (getMethodContract().getName().contains("continue_behavior")) {
            return "cont";
        } else if (getMethodContract().getName().contains("return_behavior")) {
            return "return";
        } else {
            return "";
        }
    }

    /**
     * Used to determine if the contract of this method has normal behaviour or is a model
     * field/contract and can thus not throw any exception.
     * @return true for either normal or model behaviour
     */
    public boolean isNormal() {
        return getBehaviour().equals("normal") || isModel();
    }

    /**
     * Tells whether the method is pure or not.
     * @return true for pure methods and pure (model) fields
     */
    public boolean isPure() {
        IObserverFunction target = getTarget();
        if (target instanceof IProgramMethod) {
            IProgramMethod pm = (IProgramMethod)target;
            return JMLInfoExtractor.isPure(pm);
        } else {
            return false;
        }
    }

    @Override
    public boolean isModel() {
        return this.model;
    }

    @Override
    public MethodWellDefinedness combine(WellDefinednessCheck wdc, Services services) {
        assert wdc instanceof MethodWellDefinedness;
        final MethodWellDefinedness mwd = (MethodWellDefinedness)wdc;
        assert this.getMethodContract().getName().equals(mwd.getMethodContract().getName());
        assert this.getMethodContract().id() == mwd.getMethodContract().id();
        assert this.getMethodContract().getTarget().equals(mwd.getMethodContract().getTarget());
        assert this.getMethodContract().getKJT().equals(mwd.getMethodContract().getKJT());

        super.combine(mwd, services);
        if (this.getGlobalDefs() != null && mwd.getGlobalDefs() != null) {
            final Term defs = mwd.replace(mwd.getGlobalDefs(), this.getOrigVars());
            this.globalDefs = TB.andSC(defs, this.getGlobalDefs());
        } else if (mwd.getGlobalDefs() != null) {
            final Term defs = mwd.replace(mwd.getGlobalDefs(), this.getOrigVars());
            this.globalDefs = defs;
        }
        return this;
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