/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.wd.po;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.ParameterlessTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.AbstractPO;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.ClassAxiom;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;
import de.uka.ilkd.key.wd.ClassWellDefinedness;
import de.uka.ilkd.key.wd.WellDefinednessCheck;
import de.uka.ilkd.key.wd.WellDefinednessCheck.POTerms;
import de.uka.ilkd.key.wd.WellDefinednessCheck.TermAndFunc;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * <p>
 * The proof obligation for well-definedness checks.
 * </p>
 * <p>
 * The generated {@link org.key_project.prover.sequent.Sequent} has the following form:
 *
 * <pre>
 * {@code
 * ==>
 * WD(<generalAssumptions> && <preconditions>) &
 * (<generalAssumptions> & <preconditions>
 *    -> WD(<otherClauses>) &
 *       {anon^modifiable}WD(<postconditions>)
 * }
 * </pre>
 * </p>
 *
 * @author Michael Kirsten
 */
@NullMarked
public class WellDefinednessPO extends AbstractPO implements ContractPO {

    private final WellDefinednessCheck check;
    private @Nullable JTerm mbyAtPre;
    private @Nullable InitConfig proofConfig;
    private @Nullable TermBuilder tb;

    /**
     * Constructor
     *
     * @param initConfig The initial Configuration
     * @param check The Well-Definedness Check
     */
    public WellDefinednessPO(InitConfig initConfig, WellDefinednessCheck check) {
        super(initConfig, check.getName());
        this.check = check;
    }

    // -------------------------------------------------------------------------
    // Internal Methods
    // -------------------------------------------------------------------------

    private static Function createAnonHeap(LocationVariable heap, Services services) {
        final HeapLDT heapLDT = services.getTypeConverter().getHeapLDT();
        if (heapLDT == null) {
            throw new NullPointerException(
                "No heap type defined in the services type converter.");
        }
        final Name anonHeapName =
            new Name(services.getTermBuilder().newName("anon_" + heap.toString()));
        final Function anonHeap = new JFunction(anonHeapName, heapLDT.targetSort());
        return anonHeap;
    }

    private static @Nullable LocationVariable createSelf(@Nullable IProgramMethod pm,
            KeYJavaType selfKJT, TermServices services) {
        if (pm == null) {
            return services.getTermBuilder().selfVar(selfKJT, false);
        } else {
            return services.getTermBuilder().selfVar(pm, selfKJT, true);
        }
    }

    private static @Nullable LocationVariable createResult(@Nullable IProgramMethod pm,
            TermServices services) {
        if (pm == null) {
            return null;
        } else {
            return services.getTermBuilder().resultVar(pm, true);
        }
    }

    private static @Nullable LocationVariable createException(@Nullable IProgramMethod pm,
            TermServices services) {
        if (pm == null) {
            return null;
        } else {
            return services.getTermBuilder().excVar(pm, true);
        }
    }

    private static Map<LocationVariable, @Nullable LocationVariable> createAtPres(
            LocationVariable heap,
            TermServices services) {
        final Map<LocationVariable, @Nullable LocationVariable> res =
            new LinkedHashMap<>();
        final LocationVariable atPre =
            services.getTermBuilder().atPreVar(heap.name().toString(), heap.sort(), true);
        res.put(heap, atPre);
        return res;
    }

    /** Make sure ghost parameters appear in the list of parameter variables. */
    private static ImmutableList<LocationVariable> addGhostParams(
            ImmutableList<LocationVariable> paramVars, ImmutableList<LocationVariable> origParams) {
        // make sure ghost parameters are present
        ImmutableList<LocationVariable> ghostParams = ImmutableList.nil();
        for (LocationVariable param : origParams) {
            if (param.isGhost()) {
                ghostParams = ghostParams.append(param);
            }
        }
        paramVars = paramVars.append(ghostParams);
        return paramVars;
    }

    private static ImmutableList<LocationVariable> createParams(IObserverFunction target,
            ImmutableList<LocationVariable> origParams, TermServices services) {
        final ImmutableList<LocationVariable> params =
            services.getTermBuilder().paramVars(target, true);
        return addGhostParams(params, origParams);
    }

    /**
     * This should only be executed once per proof.
     *
     * @param check the underlying well-definedness check
     * @param services
     * @return new variables to be used in the actual check
     */
    private static Variables buildVariables(WellDefinednessCheck check, Services services) {
        final OriginalVariables vars = check.getOrigVars();
        final KeYJavaType kjt = check.getKJT();
        final LocationVariable heap = check.getHeap();
        final IObserverFunction target = check.getTarget();

        final IProgramMethod pm;
        if (target instanceof IProgramMethod) {
            pm = (IProgramMethod) target;
        } else {
            pm = null;
        }
        final Function anonHeap = createAnonHeap(heap, services);
        final LocationVariable self;
        if (vars.self != null) {
            self = createSelf(pm, kjt, services);
        } else {
            self = null;
        }
        final LocationVariable result;
        if (vars.result != null) {
            result = createResult(pm, services);
        } else {
            result = null;
        }
        final LocationVariable exception;
        if (vars.exception != null) {
            exception = createException(pm, services);
        } else {
            exception = null;
        }
        final Map<LocationVariable, @Nullable LocationVariable> atPres =
            createAtPres(heap, services);
        final ImmutableList<LocationVariable> params;
        if (vars.params != null && !vars.params.isEmpty()) {
            params = createParams(target, vars.params, services);
        } else {
            params = ImmutableList.nil();
        }
        return new Variables(self, result, exception, atPres, params, heap, anonHeap, services);
    }

    /**
     * Registers the new variables
     *
     * @param vars variables to be used in the check
     */
    private void register(Variables vars, Services proofServices) {
        final JTerm anonHeap = vars.anonHeap;
        if (anonHeap == null) {
            throw new NullPointerException(
                "No anonymous heap for the well-definedness proof obligation.");
        }
        register((Function) anonHeap.op(), proofServices);
        register(vars.self, proofServices);
        register(vars.result, proofServices);
        register(vars.exception, proofServices);
        register(vars.atPres.get(vars.heap), proofServices);
        register(vars.params, proofServices);
    }

    @Override
    protected ImmutableSet<ClassAxiom> selectClassAxioms(KeYJavaType kjt) {
        ImmutableSet<ClassAxiom> result = DefaultImmutableSet.nil();
        for (ClassAxiom axiom : specRepos.getClassAxioms(kjt)) {
            if (check instanceof ClassWellDefinedness cwd) {
                final String kjtName = cwd.getKJT().getFullName();
                final String invName = "in " + cwd.getKJT().getName();
                if (!axiom.getName().endsWith(invName)
                        && !axiom.getName().endsWith(kjtName)) {
                    result = result.add(axiom);
                }
            } else {
                result = result.add(axiom);
            }
        }
        return result;
    }

    // -------------------------------------------------------------------------
    // Public Interface
    // -------------------------------------------------------------------------

    public IObserverFunction getTarget() {
        return getContract().getTarget();
    }

    public KeYJavaType getKJT() {
        return getContract().getKJT();
    }

    @Override
    public void readProblem() {
        assert proofConfig == null;

        final Services proofServices = postInit();
        final TermBuilder termBuilder = tb;
        final InitConfig config = proofConfig;
        if (termBuilder == null || config == null) {
            throw new NullPointerException(
                "Proof configuration was not initialised for the well-definedness proof obligation.");
        }

        final Variables vars = buildVariables(check, proofServices);

        register(vars, proofServices);
        final POTerms po = check.replace(check.createPOTerms(), vars);
        final TermAndFunc preCond =
            check.getPre(po.pre(), vars.self, vars.heap, vars.params, proofServices);
        final JTerm wdPre = termBuilder.wd(preCond.term());
        final JTerm wdModifiable = termBuilder.wd(po.modifiable());
        final JTerm wdRest = termBuilder.and(termBuilder.wd(po.rest()));
        register(preCond.func(), proofServices);
        mbyAtPre = preCond.func() != null
                ? check.replace(termBuilder.func(preCond.func()), vars)
                : null;
        final JTerm post = check.getPost(po.post(), vars.result, proofServices);
        final JTerm pre = preCond.term();
        final JTerm updates =
            check.getUpdates(po.modifiable(), vars.heap, vars.heapAtPre, vars.anonHeap,
                proofServices);
        final JTerm anonHeap = vars.anonHeap;
        if (anonHeap == null) {
            throw new NullPointerException(
                "No anonymous heap for the well-definedness proof obligation.");
        }
        final JTerm wfAnon = termBuilder.wellFormed(anonHeap);
        final JTerm uPost = check instanceof ClassWellDefinedness ? termBuilder.tt()
                : termBuilder.apply(updates, termBuilder.wd(post));
        final JTerm imp =
            termBuilder.imp(termBuilder.and(pre, wfAnon), termBuilder.and(wdModifiable, wdRest,
                uPost));
        final JTerm poTerms = termBuilder.and(wdPre, imp);
        assignPOTerms(poTerms);
        // add axioms
        collectClassAxioms(getKJT(), config);

        generateDynamicTaclets(config);
    }

    private Services postInit() {
        proofConfig = environmentConfig.deepCopy();
        final Services proofServices = proofConfig.getServices();
        tb = proofServices.getTermBuilder();
        return proofServices;
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof WellDefinednessPO wPO)) {
            return false;
        }
        WellDefinednessCheck check = getContract();
        return check.equals(wPO.getContract());
    }

    @Override
    public WellDefinednessCheck getContract() {
        return check;
    }

    @Override
    public JTerm getMbyAtPre() {
        final JTerm mbyAtPreTerm = this.mbyAtPre;
        if (mbyAtPreTerm == null) {
            throw new NullPointerException(
                "No measured-by-at-pre term for the well-definedness proof obligation.");
        }
        return mbyAtPreTerm;
    }

    /**
     * {@inheritDoc}
     *
     * @return
     */
    @Override
    public Configuration createLoaderConfig() {
        var c = super.createLoaderConfig();
        c.set("wd check", check.getName());
        return c;
    }

    /**
     * A static data structure for storing and passing the variables used in the actual proof. This
     * includes a self variable, a result variable, an exception variable, a mapping of heaps to the
     * according preconditions, a list of parameter variables, a base heap, a heap for the pre-state
     * and an anonymous heap.
     *
     * @author Michael Kirsten
     */
    public static class Variables {
        public final @Nullable LocationVariable self;
        public final @Nullable LocationVariable result;
        public final @Nullable LocationVariable exception;
        public final Map<LocationVariable, @Nullable LocationVariable> atPres;
        public final ImmutableList<LocationVariable> params;
        public final LocationVariable heap;
        public final LocationVariable heapAtPre;
        public final @Nullable JTerm anonHeap;

        public Variables(final @Nullable LocationVariable self,
                final @Nullable LocationVariable result,
                final @Nullable LocationVariable exception,
                final Map<LocationVariable, @Nullable LocationVariable> atPres,
                final ImmutableList<LocationVariable> params, final LocationVariable heap,
                final @Nullable JTerm anonHeap) {
            this.self = self;
            this.result = result;
            this.exception = exception;
            this.atPres = atPres;
            this.params = params;
            this.heap = heap;
            this.heapAtPre =
                (atPres == null || atPres.get(heap) == null) ? this.heap : atPres.get(heap);
            this.anonHeap = anonHeap;
        }

        private Variables(final @Nullable LocationVariable self,
                final @Nullable LocationVariable result,
                final @Nullable LocationVariable exception,
                final Map<LocationVariable, @Nullable LocationVariable> atPres,
                final ImmutableList<LocationVariable> params, final LocationVariable heap,
                final Function anonHeap, TermServices services) {
            this(self, result, exception, atPres, params, heap, services.getTermBuilder().label(
                services.getTermBuilder().func(anonHeap), ParameterlessTermLabel.ANON_HEAP_LABEL));
        }
    }

    @Override
    protected @Nullable InitConfig getCreatedInitConfigForSingleProof() {
        return proofConfig;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public KeYJavaType getContainerType() {
        return getContract().getKJT();
    }
}
