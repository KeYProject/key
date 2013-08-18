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

    private final WellDefinednessCheck check;
    private final Variables vars;
    protected Term mbyAtPre;

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

    private void register(Variables vars) {
        register((Function)vars.anonHeap.op());
        register(vars.self);
        register(vars.result);
        register(vars.exception);
        register(vars.atPres.get(vars.heap));
        register(vars.params);
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
        final TermAndFunc pre = check.getPre(po.pre, vars, services);
        register(pre.func);
        mbyAtPre = pre.func != null ? TB.func(pre.func) : TB.tt();
        final Term post = check.getPost(po.post, vars.result, services);
        final Term[] updates = check.getUpdates(po.mod, vars, services);

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

    private ImmutableSet<Taclet> generateTacletsForPV(ProgramVariable pv,
                                                      KeYJavaType kjt) {
        ImmutableSet<Taclet> res = DefaultImmutableSet.<Taclet>nil();
        for (IObserverFunction t: specRepos.getContractTargets(kjt)) {
            for (WellDefinednessCheck ch: specRepos.getWdChecks(kjt, t)) {
                if (!isJavaLangObj(ch) && ch instanceof MethodWellDefinedness) {
                    // WD(pv.m(...))
                    res = res.add(ch.createOperationTaclet(pv, vars, services));
                }
                if (!isJavaLangObj(ch)) {
                    // WD(pv.<inv>)
                    res = res.add(ch.createInvTaclet(pv, vars.heap, services));
                }
            }
        }
        register(res); // register taclets: Important!
        return res;
    }

    private ImmutableSet<Taclet> generateTaclets() {
        ImmutableSet<Taclet> res = DefaultImmutableSet.<Taclet>nil();

        // self variable
        res = res.union(generateTacletsForPV(vars.self, getKJT()));
        // result variable
        if (vars.result != null) {
            res = res.union(generateTacletsForPV(vars.result,
                                                 vars.result.getKeYJavaType()));
        }
        // program variables
        for (ProgramVariable pv: vars.params) {
            res = res.union(generateTacletsForPV(pv, pv.getKeYJavaType()));
        }
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

    private void register(ImmutableSet<Taclet> ts) {
        for (Taclet t: ts) {
            assert t != null;
            taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(t));
            initConfig.getProofEnv().registerRule(t, AxiomJustification.INSTANCE);
        }
    }

    /*private static String getBaseName(ParsableVariable pv) {
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
    }*/

    public Term getMbyAtPre() {
        return this.mbyAtPre;
    }

    private static boolean isJavaLangObj(WellDefinednessCheck ch) {
        return ch.getTarget().toString().startsWith("java.lang.Object");
    }

    public static class Variables {
        public final ProgramVariable self;
        public final ProgramVariable result;
        public final ProgramVariable exception;
        public final Map<LocationVariable, ProgramVariable> atPres;
        public final ImmutableList<ProgramVariable> params;
        public final LocationVariable heap;
        public final ProgramVariable heapAtPre;
        public final Term anonHeap;

        Variables(final ProgramVariable self,
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