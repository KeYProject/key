package de.uka.ilkd.key.proof.init;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassInvWellDefinedness;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.ClassInvariantImpl;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.MethodWellDefinedness;
import de.uka.ilkd.key.speclang.PartialInvAxiom;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.Pair;
import de.uka.ilkd.key.util.Triple;

public class WellDefinednessPO extends AbstractPO implements ContractPO {

    protected static final TermBuilder TB = TermBuilder.DF;

    private final WellDefinednessCheck check;
    private final Variables vars;

    public WellDefinednessPO(InitConfig initConfig, WellDefinednessCheck check) {
        super(initConfig, check.getName());
        this.check = check;
        this.vars = getVariables();
    }

    protected IObserverFunction getTarget() {
        return getContract().getTarget();
     }

    protected KeYJavaType getCalleeKeYJavaType() {
        return getContract().getKJT();
    }

    @Override
    public void readProblem() throws ProofInputException {
        final Triple<Pair<Term, Term>, ImmutableList<Term>, Term> po = check.createPOTerm();
        ImmutableList<Term> c = ImmutableSLList.<Term>nil();
        for (Term t: po.second) {
            c = c.append(wd(replace(t)));
        }
        final Term pre = getPre(po.first);
        final Term post = replace(po.third);
        final Term poTerms = TB.and(wd(pre), TB.imp(pre, TB.and(TB.and(c), wd(post))));
        assignPOTerms(poTerms);

        // add axioms
        collectWdClassInvariants();
        collectClassAxioms(getCalleeKeYJavaType());
    }

    @Override
    protected ImmutableSet<ClassAxiom> selectClassAxioms(KeYJavaType kjt) {
        ImmutableSet<ClassAxiom> result = DefaultImmutableSet.<ClassAxiom>nil();
        for(ClassAxiom axiom: specRepos.getClassAxioms(kjt)) {
            if(axiom instanceof PartialInvAxiom) {
                result = result.add(axiom);
            }
        }
        return result;
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof WellDefinednessPO)) {
            return false;
        }
        WellDefinednessPO wPO = (WellDefinednessPO) po;
        return specRepos.getWdChecks(wPO.check.getKJT(), wPO.check.getTarget())
                .subset(specRepos.getWdChecks(check.getKJT(), check.getTarget()));
    }

    @Override
    public WellDefinednessCheck getContract() {
        return check;
    }

    private Term getPre(final Pair<Term, Term> pre) {
        final ImmutableList<Term> res =
                buildImplicitAndFreePre(replace(pre.first)).append(replace(pre.second));
        return TB.andSC(res);
    }

    /**
     * Returns the base heap.
     * @return The {@link LocationVariable} which contains the base heap.
     */
    private LocationVariable getHeap() {
        assert this.check != null;
        return check.getHeap();
    }

    private List<LocationVariable> getHeaps() {
        List<LocationVariable> result = new ArrayList<LocationVariable>(1);
        result.add(getHeap());
        return result;
    }

    private LocationVariable getSelf() {
        IObserverFunction obs = getTarget();
        final LocationVariable self;
        if (obs instanceof IProgramMethod) {
            self = TB.selfVar(services, (IProgramMethod)obs, getCalleeKeYJavaType(), true);
            register(self);
        } else {
            self = null;
        }
        return self;
    }

    private Map<LocationVariable, ProgramVariable> getAtPres() {
        Map<LocationVariable, ProgramVariable> res =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        Map<LocationVariable, LocationVariable> atPres =
                HeapContext.getBeforeAtPreVars(getHeaps(), services, "AtPre");
        for (LocationVariable h: atPres.keySet()) {
            res.put(h, atPres.get(h));
        }
        return res;
    }

    private ProgramVariable getResult() {
        IObserverFunction obs = getTarget();
        final LocationVariable result;
        if (obs instanceof IProgramMethod) {
            result = TB.resultVar(services, (IProgramMethod)obs, true);
            register(result);
        } else {
            result = null;
        }
        return result;
    }

    private ProgramVariable getException() {
        IObserverFunction obs = getTarget();
        final LocationVariable result;
        if (obs instanceof IProgramMethod) {
            result = TB.excVar(services, (IProgramMethod)obs, true);
            register(result);
        } else {
            result = null;
        }
        return result;
    }

    /** Make sure ghost parameters appear in the list of parameter variables. */
    private ImmutableList<ProgramVariable> addGhostParams(ImmutableList<ProgramVariable> paramVars,
                                                          ImmutableList<ProgramVariable> origParams) {
        // make sure ghost parameters are present
        ImmutableList<ProgramVariable> ghostParams = ImmutableSLList.<ProgramVariable>nil();
        for (ProgramVariable param: origParams) {
            if (param.isGhost())
                ghostParams = ghostParams.append(param);
        }
        paramVars = paramVars.append(ghostParams);
        return paramVars;
    }

    private ImmutableList<ProgramVariable> getParams() {
        ImmutableList<ProgramVariable> params = TB.paramVars(services, getTarget(), true);
        return addGhostParams(params, check.getOrigVars().params);
    }

    /**
     * This should only be executed once per proof.
     * @return new variables
     */
    private Variables getVariables() {
        OriginalVariables vars = check.getOrigVars();

        final ProgramVariable self;
        final ProgramVariable result;
        final ProgramVariable exception;
        final Map<LocationVariable, ProgramVariable> atPres;
        final ImmutableList<ProgramVariable> params;

        if (vars.self != null) {
            self = getSelf();
        } else {
            self = null;
        }
        if (vars.result != null) {
            result = getResult();
        } else {
            result = null;
        }
        if (vars.exception != null) {
            exception = getException();
        } else {
            exception = null;
        }
        if (vars.atPres != null) {
            atPres = getAtPres();
        } else {
            atPres = null;
        }
        if (vars.params != null) {
            params = getParams();
        } else {
            params = null;
        }
        return new Variables(self, result, exception, atPres, params);
    }

    public Term wd(Term t) {
        return WellDefinednessCheck.wd(t, services);
    }

    private void collectWdClassInvariants() {
        IObserverFunction target = getTarget();
        KeYJavaType selfKJT = getCalleeKeYJavaType();
        ImmutableSet<ClassInvWellDefinedness> invs =
                specRepos.getWdClassInvariants(selfKJT, target);
        if(invs.isEmpty()) {
            Term inv = TB.tt();
            final SchemaVariable selfSV = target.isStatic() ?
                    null : SchemaVariableFactory.createTermSV(new Name("self"),
                                                              getCalleeKeYJavaType().getSort());
            ClassInvariant ci = new ClassInvariantImpl(name, check.getDisplayName(), selfKJT,
                                                       new Public(), inv, selfSV);
            invs = invs.add(new ClassInvWellDefinedness(ci, target, services));
        }

        for (ClassInvWellDefinedness inv : invs) {
            final Taclet invTaclet = inv.getTaclet(services);
                assert invTaclet != null : "class invariant (wd) returned null taclet: "
                                           + inv.getName();
                taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(invTaclet));
                initConfig.getProofEnv().registerRule(invTaclet,
                                                      AxiomJustification.INSTANCE);
        }
    }

    /**
     * Builds the "general assumption" using the self variable (selfVar),
     * the {@link KeYJavaType} of the self variable (selfKJT),
     * the parameters {@link ProgramVariable}s (paramVars), the heaps (heaps), and
     * @param the implicit precondition
     * @return The {@link Term} containing the general assumptions.
     */
    protected ImmutableList<Term> buildImplicitAndFreePre(Term implicitPre) {
        ProgramVariable selfVar = vars.self;
        ImmutableList<ProgramVariable> paramVars = vars.params;
        KeYJavaType selfKJT = getCalleeKeYJavaType();
        List<LocationVariable> heaps = getHeaps();
        ImmutableList<Term> res = ImmutableSLList.<Term>nil();

       // "self != null"
       final Term selfNotNull = generateSelfNotNull(selfVar);

       // "self.<created> = TRUE"
       final Term selfCreated = generateSelfCreated(heaps, selfVar);

       // "MyClass::exactInstance(self) = TRUE"
       final Term selfExactType = generateSelfExactType(selfVar, selfKJT);

       // conjunction of...
       // - "p_i.<created> = TRUE | p_i = null" for object parameters, and
       // - "inBounds(p_i)" for integer parameters
       Term paramsOK = generateParamsOK(paramVars);

       // initial value of measured_by clause
       final Term mbyAtPreDef = generateMbyAtPreDef(selfVar, paramVars);
       Term wellFormed = null;
       for (LocationVariable heap : heaps) {
          final Term wf = TB.wellFormed(TB.var(heap), services);
          if (wellFormed == null) {
             wellFormed = wf;
          }
          else {
             wellFormed = TB.and(wellFormed, wf);
          }
       }

       Term[] resultTerm = new Term[] { wellFormed != null ? wellFormed : TB.tt(), selfNotNull,
               selfCreated, selfExactType, implicitPre, paramsOK, mbyAtPreDef };
       for (Term t: resultTerm) {
           res = res.append(t);
       }
       return res;
    }

    /**
     * Generates the general assumption that self is not null.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfNotNull(ProgramVariable selfVar) {
       return selfVar == null || isConstructor() ?
              TB.tt() :
              TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
    }

    /**
     * Generates the general assumption that self is created.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfCreated(List<LocationVariable> heaps,
                                       ProgramVariable selfVar) {
           if(selfVar == null || isConstructor()) {
                   return TB.tt();
           }
           Term created = null;
           for(LocationVariable heap : heaps) {
                   if(heap == services.getTypeConverter().getHeapLDT().getSavedHeap())
                           continue;
                   final Term cr = TB.created(services, TB.var(heap), TB.var(selfVar));
                   if(created == null) {
                           created = cr;
                   }else{
                           created = TB.and(created, cr);
                   }
           }
           return created;
    }


    /**
     * Generates the general assumption which defines the type of self.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @param selfKJT The {@link KeYJavaType} of the self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfExactType(ProgramVariable selfVar,
                                         KeYJavaType selfKJT) {
       final Term selfExactType = selfVar == null || isConstructor() ?
             TB.tt() :
             TB.exactInstance(services, selfKJT.getSort(), TB.var(selfVar));
       return selfExactType;
    }

    /**
     * Generates the general assumption that all parameter arguments are valid.
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @return The term representing the general assumption.
     */
    protected Term generateParamsOK(ImmutableList<ProgramVariable> paramVars) {
       Term paramsOK = TB.tt();
       for (ProgramVariable paramVar : paramVars) {
          paramsOK = TB.and(paramsOK, TB.reachableValue(services, paramVar));
       }
       return paramsOK;
    }

    /**
     * {@inheritDoc}
     */
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars) {
        final Term mbyAtPreDef;
        final FunctionalOperationContract foc = getMethodContract();
        if (foc != null && foc.hasMby()) {
            final Function mbyAtPreFunc =
                    new Function(new Name(TB.newName(services, "mbyAtPre")),
                                 services.getTypeConverter().getIntegerLDT().targetSort());
            register(mbyAtPreFunc);
            final Term mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby = foc.getMby(selfVar, paramVars, services);
            mbyAtPreDef = TB.equals(mbyAtPre, mby);
        } else {
            mbyAtPreDef = TB.tt();
        }
        return mbyAtPreDef;
    }

    private boolean isConstructor() {
        IObserverFunction obs = getTarget();
        return obs instanceof IProgramMethod &&
                ((IProgramMethod)obs).isConstructor();
    }

    private FunctionalOperationContract getMethodContract() {
        assert this.check != null;
        if (this.check instanceof MethodWellDefinedness) {
            MethodWellDefinedness mCheck = (MethodWellDefinedness)check;
            return mCheck.getContract();
        } else {
            return null;
        }
    }

    @Deprecated
    public Term getMbyAtPre() {
        return null;
    }

    private Term replace(Term t) {
        assert this.check != null;
        return check.replace(t, vars.self, vars.result, vars.exception,
                             vars.atPres, vars.params);
    }

    private class Variables {
        protected final ProgramVariable self;
        protected final ProgramVariable result;
        protected final ProgramVariable exception;
        protected final Map<LocationVariable, ProgramVariable> atPres;
        protected final ImmutableList<ProgramVariable> params;

        Variables(final ProgramVariable self,
                  final ProgramVariable result,
                  final ProgramVariable exception,
                  final Map<LocationVariable, ProgramVariable> atPres,
                  final ImmutableList<ProgramVariable> params) {
            this.self = self;
            this.result = result;
            this.exception = exception;
            this.atPres = atPres;
            this.params = params;
        }
    }
}