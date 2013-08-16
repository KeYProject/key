package de.uka.ilkd.key.proof.init;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.AnonHeapTermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SchemaVariableFactory;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.RewriteTacletBuilder;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.MethodWellDefinedness;
import de.uka.ilkd.key.speclang.PartialInvAxiom;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.speclang.WellDefinednessCheck.POTerms;
import de.uka.ilkd.key.speclang.WellDefinednessCheck.Precondition;
import de.uka.ilkd.key.speclang.jml.JMLInfoExtractor;
import de.uka.ilkd.key.util.MiscTools;

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
        final KeYJavaType kjt = getCalleeKeYJavaType();
        final POTerms po = replace(check.createPOTerms());
        final Term pre = getPre(po.pre, getTarget());

        final Term post = getPost(po.post);
        final Term[] updates = getUpdates(po.mod);
        final Term poTerms = TB.and(wd(pre),
                                    TB.imp(pre,
                                           TB.and(wd(po.mod),
                                                  TB.and(wd(po.rest)),
                                           TB.applySequential(updates, wd(post)))));
        generateTaclets();
        assignPOTerms(poTerms);

        // add axioms
        collectClassAxioms(kjt);
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
        return check.equals(wPO.check);
    }

    @Override
    public WellDefinednessCheck getContract() {
        return check;
    }

    private Term[] getUpdates(Term mod) {
        assert mod != null;
        final Term havocUpd = TB.elementary(services, vars.heap,
                TB.anon(services, vars.heap, mod, vars.anonHeap));
        final Term oldUpd = TB.elementary(services, vars.heapAtPre, vars.heap);
        return new Term[] {oldUpd, havocUpd};
    }

    private Term getPre(final Precondition pre, IObserverFunction target) {
        final ImmutableList<Term> preTerms =
                buildImplicitAndFreePre(pre.implicit).append(pre.explicit);
        Term res = TB.andSC(preTerms);
        if (target instanceof IProgramMethod &&
                ((IProgramMethod)target).isConstructor()) {
            return appendFreePreForConstructor(res);
        } else {
            return res;
        }
    }

    private Term appendFreePreForConstructor(Term pre) {
        assert isConstructor();
        if (JMLInfoExtractor.isHelper((IProgramMethod)getTarget())) {
            return pre;
        }
        final Term self = TB.var(vars.self);
        final KeYJavaType selfKJT = getCalleeKeYJavaType();
        final Term notNull = getTarget().isStatic() ?
                TB.tt() : TB.not(TB.equals(self, TB.NULL(services)));
        final Term created = TB.created(services, vars.heap, self);
        final Term selfExactType =
                TB.exactInstance(services, selfKJT.getSort(), self);
        return TB.andSC(pre, notNull, created, selfExactType);
    }

    private Term getPost(Term post) {
        final Term implicit;
        if (vars.result != null) {
            implicit = TB.reachableValue(services, vars.result);
        } else {
            implicit = TB.tt();
        }
        return TB.andSC(implicit, post);
    }

    private Term buildAnonHeap(ProgramVariable heap) {
        final Name anonHeapName = new Name(TB.newName(services, "anon_"+heap.toString()));
        final Function anonHeapFunc = new Function(anonHeapName, heapLDT.targetSort());
        register(anonHeapFunc);
        final Term anonHeap = TB.label(TB.func(anonHeapFunc), AnonHeapTermLabel.INSTANCE);
        return anonHeap;
    }

    private ProgramVariable getSelf() {
        IObserverFunction obs = getTarget();
        final LocationVariable self;
        self = TB.selfVar(services, obs, getCalleeKeYJavaType(), true);
        register(self);
        return self;
    }

    private Map<LocationVariable, ProgramVariable> getAtPres() {
        final Map<LocationVariable, ProgramVariable> res =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        final LocationVariable heap = check.getHeap();
        final ProgramVariable atPre =
                TB.heapAtPreVar(services, heap.name()+"AtPre", heap.sort(), true);
        res.put(heap, atPre);
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

        return new Variables(self, result, exception, atPres, params, check.getHeap());
    }

    public Term wd(Term t) {
        return WellDefinednessCheck.wd(t, services);
    }

    public Term wd(Iterable<Term> l) {
        ImmutableList<Term> res = ImmutableSLList.<Term>nil();
        for (Term t: l) {
            res = res.append(wd(t));
        }
        return TB.and(res);
    }

    private Term[] wd(Term[] l) {
        Term[] res = new Term[l.length];
        for(int i = 0; i < l.length; i++) {
            res[i] = wd(l[i]);
        }
        return res;
    }

    private void generateTaclets() {
        final ImmutableSet<WellDefinednessCheck> methods =
                specRepos.getAllWdChecks();

        // WD(self.<inv>)
        buildWdInvariantTaclet(vars.self, getTarget(), getCalleeKeYJavaType());
        for (WellDefinednessCheck ch: methods) {
            buildWdMethodInvocationTaclet(vars.self, ch);
        }

        if (vars.result != null) {
            final KeYJavaType kjt = vars.result.getKeYJavaType();
            for (IObserverFunction t: specRepos.getContractTargets(kjt)) {
                // WD(result.<inv>)
                buildWdInvariantTaclet(vars.result, t, kjt);
            }
            for (WellDefinednessCheck ch: methods) {
                buildWdMethodInvocationTaclet(vars.result, ch);
            }
        }
        for (ProgramVariable pv: vars.params) {
            final KeYJavaType kjt = pv.getKeYJavaType();
            for (IObserverFunction t: specRepos.getContractTargets(kjt)) {
                // for the other program variables pv: WD(pv.<inv>)
                buildWdInvariantTaclet(pv, t, kjt);
            }
            for (WellDefinednessCheck ch: methods) {
                buildWdMethodInvocationTaclet(pv, ch);
            }
        }
    }

    private void buildWdInvariantTaclet(ProgramVariable pv,
                                        IObserverFunction target,
                                        KeYJavaType kjt) {
        final String prefix = "wd Invariant ";
        boolean isStatic = target.isStatic();
        final Term[] heaps = new Term[] {vars.heap};
        final SchemaVariable sv = target.isStatic() ?
                SchemaVariableFactory.createTermSV(new Name("self"), kjt.getSort()) :
                    SchemaVariableFactory.createTermSV(pv.name(), kjt.getSort());
        final Term var = TB.var(sv);
        final Term invTerm = isStatic ?
                TB.staticInv(services, heaps, kjt) :
                    TB.inv(services, heaps, var);
        buildTaclet(prefix, var, invTerm, target, TB.tt());
    }

    private void buildWdMethodInvocationTaclet(ProgramVariable pv,
                                               WellDefinednessCheck method) {
        final String prefix = "wd Method Invocation ";
        final IObserverFunction target = method.getTarget();
        if (target.toString().startsWith("java.lang.")) {
            return;
        }
        final boolean isStatic = target.isStatic();
        final KeYJavaType kjt = method.getKJT();
        if (pv == null) {
            if (!isStatic) {
                return;
            }
        } else if (!pv.getKeYJavaType().equals(kjt)) {
            return;
        }
        final Term pre = getPre(replace(method.getRequires()), target);
        final Term[] args = replace(getArgs(pv, vars.heap, isStatic,
                                            method.getOrigVars().params));
        final Term wdArgs = TB.and(wd(args));
        buildTaclet(prefix, args[1], TB.func(target, args), target, TB.and(wdArgs, pre));
    }

    private void buildTaclet(String prefix,
                             Term calleeVar,
                             Term callTerm,
                             IObserverFunction target,
                             Term pre) {
        final String baseName = getBaseName((ParsableVariable)calleeVar.op());
        final boolean isStatic = target.isStatic();
        if (!isStatic) {
            final String s = MiscTools.toValidTacletName(prefix) + baseName;
            for (NoPosTacletApp t: taclets) {
                if (t.taclet().name().toString().startsWith(s)) {
                    return;
                }
            }
        }
        final Name name =
                MiscTools.toValidTacletName(prefix
                                            + (isStatic ? "Static " : baseName + " ")
                                            + target.name().toString());
        final RewriteTacletBuilder tb = new RewriteTacletBuilder();
        final Term callee = calleeVar != null ?
                calleeVar :
                    TB.var(SchemaVariableFactory.createTermSV(target.name(), target.sort()));
        final Term wdCallee = isStatic ?
                TB.tt() : wd(callee);
        final Term notNull = isStatic ?
                TB.tt() : TB.not(TB.equals(callee, TB.NULL(services)));
        final Term created = isStatic ?
                TB.tt() : TB.created(services, callee);

        tb.setFind(wd(callTerm));
        tb.setName(name);
        tb.addRuleSet(new RuleSet(new Name("simplify")));
        tb.addGoalTerm(TB.andSC(notNull, wdCallee, created, pre));
        Taclet callTaclet = tb.getTaclet();
        taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(callTaclet));
        initConfig.getProofEnv().registerRule(callTaclet, AxiomJustification.INSTANCE);
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
        ImmutableList<Term> resList = ImmutableSLList.<Term>nil();

        // "self != null"
        final Term selfNotNull = generateSelfNotNull(selfVar);

        // "self.<created> = TRUE"
        final Term selfCreated = generateSelfCreated(selfVar);

        // "MyClass::exactInstance(self) = TRUE"
        final Term selfExactType = generateSelfExactType(selfVar, selfKJT);

        // conjunction of...
        // - "p_i = null | p_i.<created> = TRUE" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        Term paramsOK = generateParamsOK(paramVars);

        // initial value of measured_by clause
        final Term mbyAtPreDef = generateMbyAtPreDef(selfVar, paramVars);
        final Term wellFormed = TB.wellFormed(vars.heap, services);
        final Term[] result = new Term[]
                { wellFormed, selfNotNull, selfCreated, selfExactType,
                  implicitPre, paramsOK, mbyAtPreDef };
        for (Term t: result) {
            resList = resList.append(t);
        }
        return resList;
    }

    /**
     * Generates the general assumption that self is not null.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfNotNull(ProgramVariable selfVar) {
        return selfVar == null || isConstructor() ?
                TB.tt() : TB.not(TB.equals(TB.var(selfVar), TB.NULL(services)));
    }

    /**
     * Generates the general assumption that self is created.
     * @param pm The {@link IProgramMethod} to execute.
     * @param selfVar The self variable.
     * @return The term representing the general assumption.
     */
    protected Term generateSelfCreated(ProgramVariable selfVar) {
           if(selfVar == null || isConstructor()) {
                   return TB.tt();
           }
           return TB.created(services, vars.heap, TB.var(selfVar));
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
            return mCheck.getOperationContract();
        } else {
            return null;
        }
    }

    @Deprecated
    public Term getMbyAtPre() {
        return null;
    }

    private POTerms replace(POTerms po) {
        final Precondition pre = replace(po.pre);
        final Term mod = replace(po.mod);
        final ImmutableList<Term> rest = replace(po.rest);
        final Term post = replace(po.post);
        return check.new POTerms(pre, mod, rest, post);
    }

    private Precondition replace(Precondition pre) {
        final Term implicit = replace(pre.implicit);
        final Term explicit = replace(pre.explicit);
        return check.new Precondition(implicit, explicit);
    }

    private Term replace(Term t) {
        assert this.check != null;
        return check.replace(t, vars.self, vars.result, vars.exception,
                             vars.atPres, vars.params);
    }

    private ImmutableList<Term> replace(Iterable<Term> l) {
        ImmutableList<Term> res = ImmutableSLList.<Term>nil();
        for (Term t: l) {
            res = res.append(replace(t));
        }
        return res;
    }

    private Term[] replace(Term[] l) {
        Term[] res = new Term[l.length];
        for(int i = 0; i < l.length; i++) {
            res[i] = replace(l[i]);
        }
        return res;
    }

    private static Term[] getArgs(ParsableVariable pv,
                                  Term heap, boolean isStatic,
                                  ImmutableList<ProgramVariable> params) {
        Term[] args = new Term[params.size() + (isStatic ? 1 : 2)];
        SchemaVariable sv;
        int i = 0;
        args[i++] = heap;
        if (!isStatic) {
            sv = SchemaVariableFactory.createTermSV(
                    new Name("callee"),
                    ((ProgramVariable)pv).getKeYJavaType().getSort());
            args[i++] = TB.var(sv);
        }
        for (ProgramVariable arg : params) {
            sv = SchemaVariableFactory.createTermSV(
                    arg.name(), arg.getKeYJavaType().getSort());
            args[i++] = TB.var(sv);
        }
        return args;
    }

    private static String getBaseName(ParsableVariable pv) {
        if (pv == null) {
            return "NULL";
        }
        final String name = pv.toString();
        String baseName = name.replace("1", "")
                              .replace("2", "")
                              .replace("3", "")
                              .replace("4", "")
                              .replace("5", "")
                              .replace("6", "")
                              .replace("7", "")
                              .replace("8", "")
                              .replace("9", "")
                              .replace("0", "");
        if (baseName.endsWith("_")
                && baseName.lastIndexOf("_", 1) > 0) {
            baseName = baseName.substring(0, baseName.lastIndexOf("_", 1));
        }
        return baseName;
    }

    private class Variables {
        protected final ProgramVariable self;
        protected final ProgramVariable result;
        protected final ProgramVariable exception;
        protected final Map<LocationVariable, ProgramVariable> atPres;
        protected final ImmutableList<ProgramVariable> params;
        protected final Term heap;
        protected final Term heapAtPre;
        protected final Term anonHeap;

        Variables(final ProgramVariable self,
                  final ProgramVariable result,
                  final ProgramVariable exception,
                  final Map<LocationVariable, ProgramVariable> atPres,
                  final ImmutableList<ProgramVariable> params,
                  final LocationVariable heap) {
            this.self = self;
            this.result = result;
            this.exception = exception;
            this.atPres = atPres;
            this.params = params;
            this.heap = TB.var(heap);
            this.heapAtPre = (atPres == null || atPres.get(heap) == null) ?
                    this.heap : TB.var(atPres.get(heap));
            this.anonHeap = buildAnonHeap(heap);
        }
    }
}