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

package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.ClassWellDefinedness;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.speclang.WellDefinednessCheck.POTerms;
import de.uka.ilkd.key.speclang.WellDefinednessCheck.TermAndFunc;

/**
 * <p>
 * The proof obligation for well-definedness checks.
 * </p>
 * <p>
 * The generated {@link Sequent} has the following form:
 * <pre>
 * <code>
 * ==>
 * WD(&lt;generalAssumptions&gt; && &lt;preconditions&gt;) &
 * (&lt;generalAssumptions&gt; & &lt;preconditions&gt;
 *    -> WD(&lt;otherClauses&gt;) &
 *       {anon^assignable}WD(&lt;postconditions&gt;)
 * </code>
 * </pre>
 * </p>
 *
 * @author Michael Kirsten
 */
public class WellDefinednessPO extends AbstractPO implements ContractPO {

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
        final ImmutableList<ProgramVariable> params = TB.paramVars(services, target, true);
        return addGhostParams(params, origParams);
    }

    /**
     * This should only be executed once per proof.
     * @param check the underlying well-definedness check
     * @param services
     * @return new variables to be used in the actual check
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

    /**
     * Registers the new variables
     * @param vars variables to be used in the check
     */
    private void register(Variables vars) {
        register((Function)vars.anonHeap.op());
        register(vars.self);
        register(vars.result);
        register(vars.exception);
        register(vars.atPres.get(vars.heap));
        register(vars.params);
    }

    @Override
    protected ImmutableSet<ClassAxiom> selectClassAxioms(KeYJavaType kjt) {
        ImmutableSet<ClassAxiom> result = DefaultImmutableSet.<ClassAxiom>nil();
        for(ClassAxiom axiom: specRepos.getClassAxioms(kjt)) {
            if(axiom instanceof ClassAxiom && check instanceof ClassWellDefinedness) {
                final ClassAxiom classAxiom = (ClassAxiom)axiom;
                final ClassWellDefinedness cwd = (ClassWellDefinedness)check;
                final String kjtName = cwd.getKJT().getFullName();
                final String invName = "in " + cwd.getKJT().getName();
                if (!classAxiom.getName().endsWith(invName)
                        && !classAxiom.getName().endsWith(kjtName)) {
                    result = result.add(classAxiom);
                }
            } else {
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
        final TermAndFunc preCond =
                check.getPre(po.pre, vars.self, vars.heap, vars.params, false, services);
        final Term wdPre = TB.wd(preCond.term, services);
        final Term wdMod = TB.wd(po.mod, services);
        final Term wdRest = TB.and(TB.wd(po.rest, services));
        register(preCond.func);
        mbyAtPre = preCond.func != null ? check.replace(TB.func(preCond.func), vars) : null;
        final Term post = check.getPost(po.post, vars.result, services);
        final Term pre = preCond.term;
        final Term updates = check.getUpdates(po.mod, vars.heap, vars.heapAtPre,
                                              vars.anonHeap, services);
        final Term wfAnon = TB.wellFormed(vars.anonHeap, services);
        final Term uPost = check instanceof ClassWellDefinedness ?
                TB.tt() : TB.apply(updates, TB.wd(post, services));
        final Term imp = TB.imp(TB.and(pre, wfAnon),
                                TB.and(wdMod, wdRest, uPost));
        final Term poTerms = TB.and(wdPre, imp);
        assignPOTerms(poTerms);
        // add axioms
        collectClassAxioms(getKJT());

        generateWdTaclets();
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

    @Override
    public Term getMbyAtPre() {
        return this.mbyAtPre;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("wd check", check.getName());
    }

    /**
     * Instantiates a new proof obligation with the given settings.
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     * @throws IOException Occurred Exception.
     */
    public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties)
            throws IOException {
       String contractName = properties.getProperty("wd check");
       final Contract contract =
               initConfig.getServices().getSpecificationRepository()
                                .getContractByName(contractName);
       if (contract == null) {
           throw new RuntimeException("Contract not found: " + contractName);
       }
       else {
           final ProofOblInput po = contract.createProofObl(initConfig, contract);
           return new LoadedPOContainer(po);
       }
    }

    /**
     * A static data structure for storing and passing the variables used in the actual proof.
     * This includes a self variable, a result variable, an exception variable, a mapping of
     * heaps to the according preconditions, a list of parameter variables, a base heap,
     * a heap for the pre-state and an anonymous heap.
     *
     * @author Michael Kirsten
     */
    public static class Variables {
        public final ProgramVariable self;
        public final ProgramVariable result;
        public final ProgramVariable exception;
        public final Map<LocationVariable, ProgramVariable> atPres;
        public final ImmutableList<ProgramVariable> params;
        public final LocationVariable heap;
        public final ProgramVariable heapAtPre;
        public final Term anonHeap;

        public Variables(final ProgramVariable self,
                         final ProgramVariable result,
                         final ProgramVariable exception,
                         final Map<LocationVariable, ProgramVariable> atPres,
                         final ImmutableList<ProgramVariable> params,
                         final LocationVariable heap,
                         final Term anonHeap) {
            this.self = self;
            this.result = result;
            this.exception = exception;
            this.atPres = atPres;
            this.params = params;
            this.heap = heap;
            this.heapAtPre = (atPres == null || atPres.get(heap) == null) ?
                    this.heap : atPres.get(heap);
            this.anonHeap = anonHeap;
        }

        private Variables(final ProgramVariable self,
                          final ProgramVariable result,
                          final ProgramVariable exception,
                          final Map<LocationVariable, ProgramVariable> atPres,
                          final ImmutableList<ProgramVariable> params,
                          final LocationVariable heap,
                          final Function anonHeap) {
            this(self, result, exception, atPres, params, heap,
                 TB.label(TB.func(anonHeap), ParameterlessTermLabel.ANON_HEAP_LABEL));
        }
    }
}