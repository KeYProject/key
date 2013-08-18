package de.uka.ilkd.key.proof.init;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.AnonHeapTermLabel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.MethodWellDefinedness;
import de.uka.ilkd.key.speclang.PartialInvAxiom;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.speclang.WellDefinednessCheck.POTerms;
import de.uka.ilkd.key.speclang.WellDefinednessCheck.TermAndFunc;

public class WellDefinednessPO extends AbstractPO implements ContractPO {

    protected static final String JAVA_LANG_OBJ = "java.lang.Object";

    private final WellDefinednessCheck check;
    private final Variables vars;
    private Term mbyAtPre;

    /**
     * Constructor
     * @param initConfig The initial Configuration
     * @param check The Well-Definedness Check
     */
    public WellDefinednessPO(InitConfig initConfig, WellDefinednessCheck check) {
        super(initConfig, check.getName());
        this.check = check;
        this.vars = buildVariables(check, services);
    }

    //-------------------------------------------------------------------------
    // Internal Methods
    //-------------------------------------------------------------------------

    private static boolean isJavaLangObj(WellDefinednessCheck ch) {
        return ch.getTarget().toString().startsWith(JAVA_LANG_OBJ);
    }

    private static Function createAnonHeap(LocationVariable heap,
                                           Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        final Name anonHeapName = new Name(TB.newName(services, "anon_"+heap.toString()));
        final Function anonHeap = new Function(anonHeapName, heapLDT.targetSort());
        return anonHeap;
    }

    private static LocationVariable createSelf(IProgramMethod pm,
                                               KeYJavaType selfKJT,
                                               Services services) {
        if (pm == null) {
            return TB.selfVar(services, selfKJT, false);
        } else {
            return TB.selfVar(services, pm, selfKJT, true);
        }
    }

    private static ProgramVariable createResult(IProgramMethod pm,
                                                Services services) {
        if (pm == null) {
            return null;
        } else {
            return TB.resultVar(services, pm, true);
        }
    }

    private static ProgramVariable createException(IProgramMethod pm,
                                                   Services services) {
        if (pm == null) {
            return null;
        } else {
            return TB.excVar(services, pm, true);
        }
    }

    private static Map<LocationVariable, ProgramVariable> createAtPres(LocationVariable heap,
                                                                       Services services) {
        final Map<LocationVariable, ProgramVariable> res =
                new LinkedHashMap<LocationVariable, ProgramVariable>();
        final ProgramVariable atPre =
                TB.heapAtPreVar(services, heap.name()+"AtPre", heap.sort(), true);
        res.put(heap, atPre);
        return res;
    }

    /** Make sure ghost parameters appear in the list of parameter variables. */
    private static ImmutableList<ProgramVariable>
                            addGhostParams(ImmutableList<ProgramVariable> paramVars,
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

    private static ImmutableList<ProgramVariable> createParams(IObserverFunction target,
                                                               ImmutableList<ProgramVariable>
                                                                          origParams,
                                                               Services services) {
        final ImmutableList<ProgramVariable> params =
                TB.paramVars(services, target, true);
        return addGhostParams(params, origParams);
    }

    /**
     * This should only be executed once per proof.
     * @return new variables
     */
    private static Variables buildVariables(WellDefinednessCheck check,
                                                       Services services) {
        final OriginalVariables vars = check.getOrigVars();
        final KeYJavaType kjt = check.getKJT();
        final LocationVariable heap = check.getHeap();
        final IObserverFunction target = check.getTarget();

        final IProgramMethod pm;
        if (target instanceof IProgramMethod) {
            pm = (IProgramMethod)target;
        } else {
            pm = null;
        }
        final Function anonHeap = createAnonHeap(heap, services);
        final ProgramVariable self;
        if (vars.self != null) {
            self = createSelf(pm, kjt, services);
        } else {
            self = null;
        }
        final ProgramVariable result;
        if (vars.result != null) {
            result = createResult(pm, services);
        } else {
            result = null;
        }
        final ProgramVariable exception;
        if (vars.exception != null) {
            exception = createException(pm, services);
        } else {
            exception = null;
        }
        final Map<LocationVariable, ProgramVariable> atPres =
                createAtPres(heap, services);
        final ImmutableList<ProgramVariable> params;
        if (vars.params != null && !vars.params.isEmpty()) {
            params = createParams(target, vars.params, services);
        } else {
            params = ImmutableSLList.<ProgramVariable>nil();
        }
        return new Variables(self, result, exception, atPres, params, heap, anonHeap);
    }

    private void register(Variables vars) {
        register((Function)vars.anonHeap.op());
        register(vars.self);
        register(vars.result);
        register(vars.exception);
        register(vars.atPres.get(vars.heap));
        register(vars.params);
    }

    private void register(ImmutableSet<Taclet> ts) {
        for (Taclet t: ts) {
            assert t != null;
            taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(t));
            initConfig.getProofEnv().registerRule(t, AxiomJustification.INSTANCE);
        }
    }

    private Term[] getUpdates(Term mod) {
        assert mod != null;
        final Term havocUpd = TB.elementary(services, vars.heap,
                TB.anon(services, TB.var(vars.heap), mod, vars.anonHeap));
        final Term oldUpd = TB.elementary(services, TB.var(vars.heapAtPre), TB.var(vars.heap));
        return new Term[] {oldUpd, havocUpd};
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

    private ImmutableSet<Taclet> generateTaclets() {
        ImmutableSet<Taclet> res = DefaultImmutableSet.<Taclet>nil();
        for (WellDefinednessCheck ch: specRepos.getAllWdChecks()) {
            if (!isJavaLangObj(ch)) {
                // WD(pv.<inv>)
                res = res.add(ch.createInvTaclet(services));
                if (ch instanceof MethodWellDefinedness) {
                    MethodWellDefinedness mwd = (MethodWellDefinedness)ch;
                    // WD(pv.m(...))
                    res = res.add(mwd.createOperationTaclet(services));
                }
            }
        }
        register(res); // register taclets: Important!
        return res;
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

    //-------------------------------------------------------------------------
    // Public Interface
    //-------------------------------------------------------------------------

    public IObserverFunction getTarget() {
        return getContract().getTarget();
     }

    public KeYJavaType getKJT() {
        return getContract().getKJT();
    }

    @Override
    public void readProblem() throws ProofInputException {
        register(this.vars);
        final POTerms po = check.replace(check.createPOTerms(), vars);
        final TermAndFunc pre = check.getPre(po.pre, vars.self, vars.heap, vars.params, services);
        register(pre.func);
        mbyAtPre = pre.func != null ? TB.func(pre.func) : TB.tt();
        final Term post = getPost(po.post);
        final Term[] updates = getUpdates(po.mod);

        final Term poTerms = TB.and(TB.wd(pre.term, services),
                                    TB.imp(pre.term,
                                           TB.and(TB.wd(po.mod, services),
                                                  TB.and(TB.wd(po.rest, services)),
                                           TB.applySequential(updates, TB.wd(post, services)))));
        generateTaclets();
        assignPOTerms(poTerms);

        // add axioms
        collectClassAxioms(getKJT());
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof WellDefinednessPO)) {
            return false;
        }
        WellDefinednessPO wPO = (WellDefinednessPO) po;
        WellDefinednessCheck check = getContract();
        return check.equals(wPO.getContract());
    }

    @Override
    public WellDefinednessCheck getContract() {
        return check;
    }

    public Term getMbyAtPre() {
        return this.mbyAtPre;
    }

    public static class Variables {
        public final ProgramVariable self;
        public final ProgramVariable result;
        public final ProgramVariable exception;
        public final Map<LocationVariable, ProgramVariable> atPres;
        public final ImmutableList<ProgramVariable> params;
        final LocationVariable heap;
        final ProgramVariable heapAtPre;
        final Term anonHeap;

        private Variables(final ProgramVariable self,
                          final ProgramVariable result,
                          final ProgramVariable exception,
                          final Map<LocationVariable, ProgramVariable> atPres,
                          final ImmutableList<ProgramVariable> params,
                          final LocationVariable heap,
                          final Function anonHeap) {
            this.self = self;
            this.result = result;
            this.exception = exception;
            this.atPres = atPres;
            this.params = params;
            this.heap = heap;
            this.heapAtPre = (atPres == null || atPres.get(heap) == null) ?
                    this.heap : atPres.get(heap);
            this.anonHeap = TB.label(TB.func(anonHeap), AnonHeapTermLabel.INSTANCE);;
        }
    }
}