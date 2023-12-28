/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.label.OriginTermLabel;
import de.uka.ilkd.key.logic.label.OriginTermLabel.Origin;
import de.uka.ilkd.key.logic.label.OriginTermLabel.SpecType;
import de.uka.ilkd.key.logic.label.SymbolicExecutionTermLabel;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;
import de.uka.ilkd.key.speclang.HeapContext;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.ImmutableSet;

/**
 * <p>
 * This abstract implementation of {@link ProofOblInput} extends the functionality of
 * {@link AbstractPO} to execute some code within a try catch block.
 * </p>
 * <p>
 * The generated {@link Sequent} has the following form:
 *
 * <pre>
 * {@code
 * ==>
 * <generalAssumptions> &
 * <preconditions>
 * ->
 * <updatesToStoreInitialValues>
 * <modalityStart>
 * exc=null;
 * try {
 *   <customCode>
 * } catch (java.lang.Throwable e) {
 *    exc = e
 * }
 * <modalityEnd>
 * (exc = null & <postconditions > & <optionalUninterpretedPredicate>)
 * }
 * </pre>
 * </p>
 * <p>
 * If {@link #isAddUninterpretedPredicate()} an uninterpreted predicate is added to the
 * postcondition which contains the heap and all parameters as argument. This predicate can be used
 * to filter out invalid execution paths because its branches are closed while still open branches
 * contains valid execution paths.
 * </p>
 *
 * @author Martin Hentschel
 */
public abstract class AbstractOperationPO extends AbstractPO {
    private static final String JAVA_LANG_THROWABLE = "java.lang.Throwable";

    protected InitConfig proofConfig;

    /**
     * If this is {@code true} an uninterpreted predicate is added to the postconditions which
     * contains the heap and all parameters as arguments.
     *
     * @see #createUninterpretedPredicate(ImmutableList, Term, String, Services)
     * @see #getUninterpretedPredicateName()
     */
    private final boolean addUninterpretedPredicate;

    /**
     * If this is {@code true} the {@link SymbolicExecutionTermLabel} will be added to the initial
     * modality which is proven.
     */
    private final boolean addSymbolicExecutionLabel;

    /**
     * The used uninterpreted predicate created via
     * {@link #createUninterpretedPredicate(ImmutableList, Term, String, Services)} and available
     * via {@link #getUninterpretedPredicate()}.
     */
    private Term uninterpretedPredicate;

    /**
     * Additional uninterpreted predicates, e.g. used in the validity branch of applied block
     * contracts.
     */
    private final Set<Term> additionalUninterpretedPredicates = new HashSet<>();


    /**
     * Constructor.
     *
     * @param initConfig The {@link InitConfig} to use.
     * @param name The name to use.
     */
    public AbstractOperationPO(InitConfig initConfig, String name) {
        this(initConfig, name, false, false);
    }

    /**
     * Constructor.
     *
     * @param initConfig The {@link InitConfig} to use.
     * @param name he name to use.
     * @param addUninterpretedPredicate {@code true} postcondition contains uninterpreted predicate,
     *        {@code false} uninterpreted predicate is not contained in postcondition.
     * @param addSymbolicExecutionLabel {@code true} to add the {@link SymbolicExecutionTermLabel}
     *        to the modality, {@code false} to not label the modality.
     */
    public AbstractOperationPO(InitConfig initConfig, String name,
            boolean addUninterpretedPredicate, boolean addSymbolicExecutionLabel) {
        super(initConfig, name);
        this.addUninterpretedPredicate = addUninterpretedPredicate;
        this.addSymbolicExecutionLabel = addSymbolicExecutionLabel;
    }

    /**
     * Returns the uninterpreted predicate used in the given {@link Proof} if available.
     *
     * @param proof The {@link Proof} to get its uninterpreted predicate.
     * @return The uninterpreted predicate or {@code null} if not used.
     */
    public static Term getUninterpretedPredicate(Proof proof) {
        if (proof != null && !proof.isDisposed()) {
            ProofOblInput problem =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);
            if (problem instanceof AbstractOperationPO operationPO) {
                if (operationPO.isAddUninterpretedPredicate()) {
                    return operationPO.getUninterpretedPredicate();
                }
            }
        }
        return null;
    }

    /**
     * Returns the uninterpreted predicate used in the given {@link Proof} if available.
     *
     * @param proof The {@link Proof} to get its uninterpreted predicate.
     * @return The uninterpreted predicate or {@code null} if not used.
     */
    public static Set<Term> getAdditionalUninterpretedPredicates(Proof proof) {
        if (proof != null && !proof.isDisposed()) {
            ProofOblInput problem =
                proof.getServices().getSpecificationRepository().getProofOblInput(proof);
            if (problem instanceof AbstractOperationPO operationPO) {
                if (operationPO.isAddUninterpretedPredicate()) {
                    return operationPO.getAdditionalUninterpretedPredicates();
                }
            }
        }
        return null;
    }

    /**
     * This method adds the uninterpreted predicate to the given {@link Term} if the used
     * {@link ProofOblInput} is an instance of {@link AbstractOperationPO} and
     * {@link AbstractOperationPO#isAddUninterpretedPredicate()} is {@code true}. Otherwise the
     * given {@link Term} is returned.
     *
     * @param services The {@link Services} which provides the {@link Proof} and its
     *        {@link ProofOblInput}.
     * @param term The {@link Term} to modify.
     * @return The modified or original {@link Term}.
     */
    public static Term addUninterpretedPredicateIfRequired(Services services, Term term) {
        ProofOblInput problem =
            services.getSpecificationRepository().getProofOblInput(services.getProof());
        if (problem instanceof AbstractOperationPO operationPO) {
            if (operationPO.isAddUninterpretedPredicate()) {
                term = services.getTermBuilder().and(term, operationPO.getUninterpretedPredicate());
            }
        }
        return term;
    }

    /**
     * This method adds the uninterpreted predicate to the given {@link Term} if the used
     * {@link ProofOblInput} is an instance of {@link AbstractOperationPO} and
     * {@link AbstractOperationPO#isAddUninterpretedPredicate()} is {@code true}. Otherwise the
     * given {@link Term} is returned.
     *
     * @param services The {@link Services} which provides the {@link Proof} and its
     *        {@link ProofOblInput}.
     * @param term The {@link Term} to modify.
     * @param variablesToProtect {@link LocationVariable}s to protect.
     * @param exceptionVar The exception variable to protect.
     * @return The modified or original {@link Term}.
     */
    public static Term addAdditionalUninterpretedPredicateIfRequired(Services services, Term term,
            ImmutableList<LocationVariable> variablesToProtect, Term exceptionVar) {
        ProofOblInput problem =
            services.getSpecificationRepository().getProofOblInput(services.getProof());
        if (problem instanceof AbstractOperationPO operationPO) {
            if (operationPO.isAddUninterpretedPredicate()) {
                Term up = operationPO.newAdditionalUninterpretedPredicate(variablesToProtect,
                    exceptionVar, operationPO.getUninterpretedPredicateName(), services);
                term = services.getTermBuilder().and(term, up);
            }
        }
        return term;
    }

    /**
     * Checks if the "addUninterpretedPredicate" value is set in the given {@link Properties}.
     *
     * @param properties The {@link Properties} to read value from.
     * @return {@code true} is set, {@code false} is not set.
     */
    public static boolean isAddUninterpretedPredicate(Configuration properties) {
        String value = properties.getString(IPersistablePO.PROPERTY_ADD_UNINTERPRETED_PREDICATE);
        return value != null && !value.isEmpty() ? Boolean.parseBoolean(value) : false;
    }

    /**
     * Checks if the "addSymbolicExecutionLabel" value is set in the given {@link Properties}.
     *
     * @param properties The {@link Properties} to read value from.
     * @return {@code true} is set, {@code false} is not set.
     */
    public static boolean isAddSymbolicExecutionLabel(Configuration properties) {
        String value = properties.getString(IPersistablePO.PROPERTY_ADD_SYMBOLIC_EXECUTION_LABEL);
        return value != null && !value.isEmpty() ? Boolean.parseBoolean(value) : false;
    }

    private static void collectHeapAtPres(final List<LocationVariable> modHeaps,
            final Map<LocationVariable, LocationVariable> atPreVars, final TermBuilder tb) {
        final Map<LocationVariable, Map<Term, Term>> heapToAtPre =
            new LinkedHashMap<>();
        for (LocationVariable heap : modHeaps) {
            heapToAtPre.put(heap, new LinkedHashMap<>());
            heapToAtPre.get(heap).put(tb.var(heap), tb.var(atPreVars.get(heap)));
        }
    }

    private static Term[] createUpdateSubs(final IObserverFunction target,
            final ProgramVariable selfVar, final ImmutableList<ProgramVariable> paramVars,
            final List<LocationVariable> modHeaps,
            final Map<LocationVariable, LocationVariable> atPreVars, final TermBuilder tb) {
        final Term[] updateSubs = new Term[target.arity()];
        int i = 0;
        for (LocationVariable heap : modHeaps) {
            if (target.getStateCount() >= 1) {
                updateSubs[i] = tb.var(heap);
                i++;
                if (target.getStateCount() == 2) {
                    updateSubs[i] = tb.var(atPreVars.get(heap));
                    i++;
                }
            }
        }
        if (!target.isStatic()) {
            updateSubs[i] = tb.var(selfVar);
            i++;
        }
        for (ProgramVariable paramVar : paramVars) {
            updateSubs[i] = tb.var(paramVar);
            i++;
        }
        return updateSubs;
    }

    private static Term createPermsFor(final IProgramMethod pm, final List<LocationVariable> heaps,
            final Services proofServices, final TermBuilder tb) {
        Term permsFor = tb.tt();
        if (pm.getHeapCount(proofServices) == 2
                && proofServices.getTypeConverter().getHeapLDT().getPermissionHeap() != null) {
            int stateCount = pm.getStateCount();
            for (int i = 0; i < stateCount; i++) {
                LocationVariable h = heaps.get(i);
                LocationVariable p = heaps.get(i + stateCount);
                final Term pf = tb.permissionsFor(p, h);
                permsFor = tb.and(permsFor, pf);
            }
        }
        return permsFor;
    }

    private static List<LocationVariable> addPreHeaps(final IObserverFunction target,
            final List<LocationVariable> modHeaps,
            final Map<LocationVariable, LocationVariable> atPreVars) {
        final List<LocationVariable> heaps = new ArrayList<>();
        for (LocationVariable heap : modHeaps) {
            if (target.getStateCount() >= 1) {
                heaps.add(heap);
                if (target.getStateCount() == 2) {
                    heaps.add(atPreVars.get(heap));
                }
            }
        }
        return heaps;
    }

    private static Term saveBeforeHeaps(final Map<Term, Term> heapToBefore, final TermBuilder tb) {
        Term saveBeforeHeaps = null;
        for (Term heap : heapToBefore.keySet()) {
            final Term bu = tb.elementary(heapToBefore.get(heap), heap);
            if (saveBeforeHeaps == null) {
                saveBeforeHeaps = bu;
            } else {
                saveBeforeHeaps = tb.parallel(saveBeforeHeaps, bu);
            }
        }
        return saveBeforeHeaps;
    }

    private static Map<Term, Term> createHeapToAtPres(final List<LocationVariable> modHeaps,
            final Map<LocationVariable, LocationVariable> atPreVars, final TermBuilder tb) {
        final Map<Term, Term> heapToAtPre = new LinkedHashMap<>();
        for (LocationVariable heap : modHeaps) {
            heapToAtPre.put(tb.var(heap), tb.var(atPreVars.get(heap)));
        }
        return heapToAtPre;
    }

    private static Term addTransactionPrecondition(Term pre, boolean transactionFlag,
            final boolean isTransactionApplicable, final Services proofServices,
            final TermBuilder tb) {
        if (isTransactionApplicable) {
            // Need to add assumptions about the transaction depth
            try {
                final Term depthTerm = proofServices.getJavaInfo().getStaticProgramMethodTerm(
                    "getTransactionDepth", new Term[0], "javacard.framework.JCSystem");
                final Term depthValue = transactionFlag ? tb.one() : tb.zero();
                pre = tb.and(pre, tb.equals(depthTerm, depthValue));
            } catch (IllegalArgumentException iae) {
                throw new IllegalStateException(
                    "You are trying to prove a contract that involves Java Card "
                        + "transactions, but the required Java Card API classes are not "
                        + "in your project.");
            }
        }
        return pre;
    }

    private static Term createProgPost(final IObserverFunction target,
            final ProgramVariable selfVar, final ImmutableList<ProgramVariable> paramVars,
            final ProgramVariable resultVar, final List<LocationVariable> modHeaps,
            final Map<LocationVariable, LocationVariable> atPreVars, final Term saveBeforeHeaps,
            final Term representsFromContract, final Term post, final TermBuilder tb) {
        final Term progPost;
        if (representsFromContract == null) {
            final Term[] updateSubs =
                createUpdateSubs(target, selfVar, paramVars, modHeaps, atPreVars, tb);
            progPost = tb.apply(saveBeforeHeaps,
                tb.apply(tb.elementary(tb.var(resultVar), tb.func(target, updateSubs)), post));
        } else {
            final Term body = representsFromContract;
            assert body.op() == Equality.EQUALS
                    : "Only fully functional represents clauses for model"
                        + " methods are supported!";
            progPost = tb.apply(saveBeforeHeaps,
                tb.apply(tb.elementary(tb.var(resultVar), body.sub(1)), post));
        }
        return progPost;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;
        final Services proofServices = postInit();
        final IProgramMethod pm = getProgramMethod();
        List<Term> termPOs = new ArrayList<>();

        // prepare variables, program method
        boolean makeNamesUnique = isMakeNamesUnique();
        final ImmutableList<ProgramVariable> paramVars = tb.paramVars(pm, makeNamesUnique);
        final ProgramVariable selfVar = tb.selfVar(pm, getCalleeKeYJavaType(), makeNamesUnique);
        final ProgramVariable resultVar = tb.resultVar(pm, makeNamesUnique);
        final ProgramVariable exceptionVar = tb.excVar(pm, makeNamesUnique);

        if (pm.isModel()) {
            // before resultVar
            final List<LocationVariable> modHeaps = HeapContext.getModHeaps(proofServices, false);
            final Map<LocationVariable, LocationVariable> atPreVars =
                HeapContext.getBeforeAtPreVars(modHeaps, proofServices, "AtPre");
            collectHeapAtPres(modHeaps, atPreVars, tb);

            register(paramVars, new ProgramVariable[] { selfVar, resultVar }, atPreVars.values(),
                proofServices);

            final Term poTerm = createModelPOTerm(pm, selfVar, paramVars, resultVar, modHeaps,
                atPreVars, proofServices);
            termPOs.add(poTerm);
        } else {
            // This should be indented, but for now I want to make diffing a bit easier
            final boolean[] transactionFlags = setTransactionFlags();
            int nameIndex = 0;
            for (boolean transactionFlag : transactionFlags) {
                // prepare heapAtPre
                final List<LocationVariable> modHeaps =
                    HeapContext.getModHeaps(proofServices, transactionFlag);
                final Map<LocationVariable, LocationVariable> atPreVars =
                    HeapContext.getBeforeAtPreVars(modHeaps, proofServices, "AtPre");

                // FIXME Wojtek: This is a fiddly bit that needs to be rechecked eventually
                /*
                 * if (modHeaps.contains(getSavedHeap())) { heapToAtPre.get(getSavedHeap())
                 * .put(tb.getBaseHeap(), tb.var(atPreVars.get(getSavedHeap()))); }
                 */

                register(paramVars, new ProgramVariable[] { selfVar, resultVar, exceptionVar },
                    atPreVars.values(), proofServices);

                final Term applyGlobalUpdate = createNonModelPOTerm(pm, selfVar, paramVars,
                    resultVar, exceptionVar, transactionFlag, modHeaps, atPreVars, proofServices);
                termPOs.add(applyGlobalUpdate);
                if (poNames != null) {
                    poNames[nameIndex] = buildPOName(transactionFlag);
                    nameIndex++;
                }
            } // for(boolean transactionFlag : transactionFlags)
        }
        // initalize OriginTermLabels
        termPOs = termPOs.stream().map(t -> OriginTermLabel.collectSubtermOrigins(t, proofServices))
                .collect(Collectors.toList());

        // save in field
        assignPOTerms(termPOs.toArray(new Term[0]));

        // add axioms
        collectClassAxioms(getCalleeKeYJavaType(), proofConfig);

        // for JML annotation statements
        generateWdTaclets(proofConfig);
    }

    /**
     * Checks if an uninterpreted predicate is added to the postcondition or not.
     *
     * @return {@code true} postcondition contains uninterpreted predicate, {@code false}
     *         uninterpreted predicate is not contained in postcondition.
     */
    public boolean isAddUninterpretedPredicate() {
        return addUninterpretedPredicate;
    }

    /**
     * Checks if the modality is labeled with the {@link SymbolicExecutionTermLabel}.
     *
     * @return {@code true} modality is labled, {@code false} modality is not labled.
     */
    public boolean isAddSymbolicExecutionLabel() {
        return addSymbolicExecutionLabel;
    }

    /**
     * Returns the used uninterpreted predicate.
     *
     * @return The used uninterpreted predicate.
     */
    public Term getUninterpretedPredicate() {
        return uninterpretedPredicate;
    }

    /**
     * Returns the available additional uninterpreted predicates.
     *
     * @return The available additional uninterpreted predicates.
     */
    public Set<Term> getAdditionalUninterpretedPredicates() {
        return additionalUninterpretedPredicates;
    }


    /**
     * {@inheritDoc}
     *
     * @return
     */
    @Override
    public Configuration createLoaderConfig() {
        var c = super.createLoaderConfig();
        if (isAddUninterpretedPredicate()) {
            c.set(IPersistablePO.PROPERTY_ADD_UNINTERPRETED_PREDICATE,
                String.valueOf(isAddUninterpretedPredicate()));
        }
        if (isAddSymbolicExecutionLabel()) {
            c.set(IPersistablePO.PROPERTY_ADD_SYMBOLIC_EXECUTION_LABEL,
                String.valueOf(isAddSymbolicExecutionLabel()));
        }
        return c;
    }

    public ImmutableSet<NoPosTacletApp> getInitialTaclets() {
        return taclets;
    }

    @Override
    protected InitConfig getCreatedInitConfigForSingleProof() {
        return proofConfig;
    }

    protected Services postInit() {
        proofConfig = environmentConfig.deepCopy();
        final Services proofServices = proofConfig.getServices();
        tb = proofServices.getTermBuilder();
        return proofServices;
    }

    /**
     * Modifies the post condition with help of
     * {@link POExtension#modifyPostTerm(InitConfig, Services, Term)}.
     *
     * @param proofServices The {@link Services} to use.
     * @param post The post condition to modify.
     * @return The modified post condition or the original one if no modifications were performed.
     */
    protected Term modifyPostTerm(Services proofServices, Term post) {
        ImmutableList<POExtension> extensions = ProofInitServiceUtil.getOperationPOExtension(this);
        for (POExtension extension : extensions) {
            post = extension.modifyPostTerm(proofConfig, proofServices, post);
        }
        return post;
    }

    /**
     * Checks if self variable, exception variable, result variable and method call arguments should
     * be renamed to make sure that their names are unique in the whole KeY application.
     *
     * @return {@code true} use unique names, {@code false} use original names even if they are not
     *         unique in whole KeY application.
     */
    protected boolean isMakeNamesUnique() {
        // Changing this behaviour to fix #1552.
        // return true;
        return false;
    }

    /**
     * Returns the {@link IProgramMethod} to call.
     *
     * @return The {@link IProgramMethod} to call.
     */
    protected abstract IProgramMethod getProgramMethod();

    /**
     * Checks if transactions are applicable.
     *
     * @return Transactions are applicable?
     */
    protected abstract boolean isTransactionApplicable();

    /**
     * Returns the {@link KeYJavaType} which contains {@link #getProgramMethod()}.
     *
     * @return The {@link KeYJavaType} which contains {@link #getProgramMethod()}.
     */
    protected abstract KeYJavaType getCalleeKeYJavaType();

    /**
     * Builds the code to execute in different statement blocks. 1. code to execute before the try
     * block 2. code to execute in the try block 3. code to execute in the catch block 4. code to
     * execute in the finally block
     *
     * @param formalParVars Arguments from formal parameters for method call.
     * @param selfVar The self variable.
     * @param resultVar The result variable.
     * @param services services instance
     * @return operation blocks as statement blocks
     */
    protected abstract ImmutableList<StatementBlock> buildOperationBlocks(
            ImmutableList<LocationVariable> formalParVars, ProgramVariable selfVar,
            ProgramVariable resultVar, Services services);


    /**
     * Builds the "general assumption".
     *
     * @param selfVar The self variable.
     * @param selfKJT The {@link KeYJavaType} of the self variable.
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @param heaps The heaps.
     * @param services The services instance.
     * @return The {@link Term} containing the general assumptions.
     */
    protected Term buildFreePre(ProgramVariable selfVar, KeYJavaType selfKJT,
            ImmutableList<ProgramVariable> paramVars, List<LocationVariable> heaps,
            Services services) {
        // "self != null"
        final Term selfNotNull = generateSelfNotNull(getProgramMethod(), selfVar);

        // "self.<created> = TRUE"
        final Term selfCreated = generateSelfCreated(heaps, getProgramMethod(), selfVar, services);

        // "MyClass::exactInstance(self) = TRUE"
        final Term selfExactType = generateSelfExactType(getProgramMethod(), selfVar, selfKJT);

        // conjunction of...
        // - "p_i = null | p_i.<created> = TRUE" for object parameters, and
        // - "inBounds(p_i)" for integer parameters
        Term paramsOK = generateParamsOK(paramVars);

        // initial value of measured_by clause
        final Term mbyAtPreDef = generateMbyAtPreDef(selfVar, paramVars, services);
        Term wellFormed = null;
        for (LocationVariable heap : heaps) {
            final Term wf = tb.wellFormed(tb.var(heap));
            if (wellFormed == null) {
                wellFormed = wf;
            } else {
                wellFormed = tb.and(wellFormed, wf);
            }
        }

        Term result = tb.and(wellFormed != null ? wellFormed : tb.tt(), selfNotNull, selfCreated,
            selfExactType, paramsOK, mbyAtPreDef);

        return tb.addLabelToAllSubs(result, new Origin(SpecType.REQUIRES));
    }

    /**
     * Generates the general assumption that all parameter arguments are valid.
     *
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @return The term representing the general assumption.
     */
    protected Term generateParamsOK(ImmutableList<ProgramVariable> paramVars) {
        Term paramsOK = tb.tt();
        for (ProgramVariable paramVar : paramVars) {
            paramsOK = tb.and(paramsOK, tb.reachableValue(paramVar));
        }
        return paramsOK;
    }

    /**
     * Generates the general assumption that all parameter arguments are valid.
     *
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @return The term representing the general assumption.
     */
    protected Term generateParamsOK2(ImmutableList<Term> paramVars) {
        Term paramsOK = tb.tt();
        for (Term paramVar : paramVars) {
            assert paramVar.op() instanceof ProgramVariable;
            ProgramVariable pv = (ProgramVariable) paramVar.op();
            paramsOK = tb.and(paramsOK, tb.reachableValue(pv));
        }
        return paramsOK;
    }

    protected abstract Term generateMbyAtPreDef(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services);

    /**
     * Creates the precondition.
     *
     * @param modHeaps The heaps.
     * @param selfVar The self variable.
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @param atPreVars Mapping of {@link LocationVariable} to the {@link LocationVariable} which
     *        contains the initial value.
     * @param services The {@link Services} to use.
     * @return The {@link Term} representing the precondition.
     */
    protected abstract Term getPre(List<LocationVariable> modHeaps, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services);

    /**
     * Creates the postcondition.
     *
     * @param modHeaps The heaps.
     * @param selfVar The self variable.
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @param resultVar The result variable.
     * @param exceptionVar The exception variable.
     * @param atPreVars Mapping of {@link LocationVariable} to the {@link LocationVariable} which
     *        contains the initial value.
     * @param services The {@link Services} to use.
     * @return The {@link Term} representing the postcondition.
     */
    protected abstract Term getPost(List<LocationVariable> modHeaps, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, ProgramVariable resultVar,
            ProgramVariable exceptionVar, Map<LocationVariable, LocationVariable> atPreVars,
            Services services);

    protected abstract Term getGlobalDefs(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Services services);

    /**
     * Returns the name used for the uninterpreted predicate.
     *
     * @return The name of the uninterpreted predicate.
     */
    protected String getUninterpretedPredicateName() {
        return "SETAccumulate";
    }

    /**
     * Creates {@link #uninterpretedPredicate}.
     *
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @param formalParamVars The formal parameters {@link LocationVariable}s.
     * @param exceptionVar The exception variable.
     * @param name The name of the uninterpreted predicate.
     * @param services services instance.
     * @return The created uninterpreted predicate.
     */
    protected Term ensureUninterpretedPredicateExists(ImmutableList<ProgramVariable> paramVars,
            ImmutableList<LocationVariable> formalParamVars, ProgramVariable exceptionVar,
            String name, Services services) {
        // Make sure that the predicate is not already created
        if (uninterpretedPredicate != null) {
            throw new IllegalStateException("The uninterpreted predicate is already available.");
        }
        uninterpretedPredicate =
            createUninterpretedPredicate(formalParamVars, tb.var(exceptionVar), name, services);
        return uninterpretedPredicate;
    }

    /**
     * Creates a new uninterpreted predicate which is added to
     * {@link #additionalUninterpretedPredicates}.
     *
     * @param formalParamVars The formal parameters {@link LocationVariable}s.
     * @param exceptionVar The exception variable.
     * @param name The name of the uninterpreted predicate.
     * @param services services instance.
     * @return The created uninterpreted predicate.
     */
    protected Term newAdditionalUninterpretedPredicate(
            ImmutableList<LocationVariable> formalParamVars, Term exceptionVar, String name,
            Services services) {
        Term up = createUninterpretedPredicate(formalParamVars, exceptionVar, name, services);
        additionalUninterpretedPredicates.add(up);
        return up;
    }

    /**
     * Creates a {@link Term} to use in the postcondition of the generated {@link Sequent} which
     * represents the uninterpreted predicate.
     *
     * @param formalParamVars The formal parameters {@link LocationVariable}s.
     * @param exceptionVar The exception variable.
     * @param name The name of the uninterpreted predicate.
     * @param services services instance.
     * @return The created uninterpreted predicate.
     */
    protected Term createUninterpretedPredicate(ImmutableList<LocationVariable> formalParamVars,
            Term exceptionVar, String name, Services services) {
        // Create parameters for predicate
        // SETAccumulate(HeapSort, MethodParameter1Sort, ... MethodParameterNSort)
        ImmutableList<Term> arguments = ImmutableSLList.nil(); // tb.var(paramVars);
        // Method parameters
        for (LocationVariable formalParam : formalParamVars) {
            arguments = arguments.prepend(tb.var(formalParam));
        }
        // Exception variable (As second argument for the predicate)
        arguments = arguments.prepend(exceptionVar);
        // Heap (As first argument for the predicate)
        arguments = arguments.prepend(tb.getBaseHeap());
        // Create non-rigid predicate with signature:
        // SETAccumulate(HeapSort, MethodParameter1Sort, ... MethodParameterNSort)
        ImmutableList<Sort> argumentSorts = tb.getSorts(arguments);
        Function f = new Function(new Name(tb.newName(name)), Sort.FORMULA,
            argumentSorts.toArray(new Sort[argumentSorts.size()]));
        services.getNamespaces().functions().addSafely(f);
        // Create term that uses the new predicate
        return services.getTermBuilder().func(f, arguments.toArray(new Term[arguments.size()]));
    }

    /**
     * Builds the frame clause including the modifies clause.
     *
     * @param modHeaps The heaps.
     * @param heapToAtPre The previous heap before execution.
     * @param selfVar The self variable.
     * @param paramVars The parameters {@link ProgramVariable}s.
     * @param services services instance
     * @return The created {@link Term} representing the frame clause.
     */
    protected abstract Term buildFrameClause(List<LocationVariable> modHeaps,
            Map<Term, Term> heapToAtPre, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services);

    /**
     * Creates the {@link Term} which contains the modality including the complete program to
     * execute.
     *
     * @param paramVars Formal parameters of method call.
     * @param formalParamVars Arguments from formal parameters for method call.
     * @param selfVar The self variable.
     * @param resultVar The result variable.
     * @param exceptionVar The {@link ProgramVariable} used to store caught exceptions.
     * @param atPreVars Mapping of {@link LocationVariable} to the {@link LocationVariable} which
     *        contains the initial value.
     * @param postTerm The post condition.
     * @param sb The {@link StatementBlock} to execute in try block.
     * @param services services instance.
     * @return The created {@link Term}.
     */
    protected Term buildProgramTerm(ImmutableList<ProgramVariable> paramVars,
            ImmutableList<LocationVariable> formalParamVars, ProgramVariable selfVar,
            ProgramVariable resultVar, ProgramVariable exceptionVar,
            Map<LocationVariable, LocationVariable> atPreVars, Term postTerm,
            ImmutableList<StatementBlock> sb, Services services) {

        // create java block
        final JavaBlock jb = buildJavaBlock(formalParamVars, selfVar, resultVar, exceptionVar,
            atPreVars.containsKey(getSavedHeap(services)), sb);

        // create program term
        Term programTerm = tb.prog(getTerminationMarker(), jb, postTerm);

        // label modality if required
        if (addSymbolicExecutionLabel) {
            int labelID = services.getCounter(SymbolicExecutionTermLabel.PROOF_COUNTER_NAME)
                    .getCountPlusPlus();
            programTerm = tb.label(programTerm, new SymbolicExecutionTermLabel(labelID));
        }

        // create update
        Term update = buildUpdate(paramVars, formalParamVars, atPreVars, services);

        return tb.apply(update, programTerm, null);
    }

    /**
     * Returns the base heap.
     *
     * @param services services instance.
     * @return The {@link LocationVariable} of the base heap.
     */
    protected LocationVariable getBaseHeap(Services services) {
        return services.getTypeConverter().getHeapLDT().getHeap();
    }

    /**
     * Returns the saved heap.
     *
     * @param services services instance.
     * @return The {@link LocationVariable} of the saved heap.
     */
    protected LocationVariable getSavedHeap(Services services) {
        return services.getTypeConverter().getHeapLDT().getSavedHeap();
    }

    /**
     * Creates the try catch block to execute.
     *
     * @param formalParVars Arguments from formal parameters for method call.
     * @param selfVar The self variable.
     * @param resultVar The result variable.
     * @param exceptionVar The {@link ProgramVariable} used to store caught exceptions.
     * @param transaction Transaction flag.
     * @param sb The {@link StatementBlock}s to execute.
     * @return The created {@link JavaBlock} which contains the try catch block.
     */
    protected JavaBlock buildJavaBlock(ImmutableList<LocationVariable> formalParVars,
            ProgramVariable selfVar, ProgramVariable resultVar, ProgramVariable exceptionVar,
            boolean transaction, ImmutableList<StatementBlock> sb) {
        assert sb.size() == 4 : "wrong number of blocks in method";
        final StatementBlock beforeTry = sb.head();
        final StatementBlock tryBlock = sb.tail().head();
        final StatementBlock catchBlock = sb.tail().tail().head();
        final StatementBlock finallyBlock = sb.tail().tail().tail().head();

        // create variables for try statement
        // changed from Exception to Throwable (issue #1379)
        final KeYJavaType eType = javaInfo.getTypeByClassName(JAVA_LANG_THROWABLE);
        final TypeReference excTypeRef = javaInfo.createTypeReference(eType);
        final ProgramElementName ePEN = new ProgramElementName("e");
        final ProgramVariable eVar = new LocationVariable(ePEN, eType);

        final StatementBlock sb2;
        if (exceptionVar == null) {
            sb2 = tryBlock;
        } else {
            // create try statement
            final CopyAssignment nullStat = new CopyAssignment(exceptionVar, NullLiteral.NULL);
            final VariableSpecification eSpec = new VariableSpecification(eVar);
            final ParameterDeclaration excDecl =
                new ParameterDeclaration(new Modifier[0], excTypeRef, eSpec, false);
            final CopyAssignment assignStat = new CopyAssignment(exceptionVar, eVar);
            final Catch catchStat =
                new Catch(excDecl, catchBlock == null ? new StatementBlock(assignStat)
                        : new StatementBlock(assignStat, catchBlock));
            final Branch[] branches = finallyBlock == null ? new Branch[] { catchStat }
                    : new Branch[] { catchStat, new Finally(finallyBlock) };
            final Try tryStat = new Try(tryBlock, branches);
            if (beforeTry == null) {
                sb2 = new StatementBlock(transaction
                        ? new Statement[] {
                            new TransactionStatement(
                                de.uka.ilkd.key.java.recoderext.TransactionStatement.BEGIN),
                            nullStat, tryStat,
                            new TransactionStatement(
                                de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH) }
                        : new Statement[] { nullStat, tryStat });
            } else {
                sb2 = new StatementBlock(transaction
                        ? new Statement[] {
                            new TransactionStatement(
                                de.uka.ilkd.key.java.recoderext.TransactionStatement.BEGIN),
                            nullStat, beforeTry, tryStat,
                            new TransactionStatement(
                                de.uka.ilkd.key.java.recoderext.TransactionStatement.FINISH) }
                        : new Statement[] { nullStat, beforeTry, tryStat });
            }
        }
        // create java block
        JavaBlock result = JavaBlock.createJavaBlock(sb2);
        return result;
    }

    /**
     * Returns the {@link Modality} to use as termination marker.
     *
     * @return The {@link Modality} to use as termination marker.
     */
    protected abstract Modality getTerminationMarker();

    /**
     * Builds the initial updates.
     *
     * @param paramVars Formal parameters of method call.
     * @param formalParamVars Arguments from formal parameters for method call.
     * @param atPreVars Mapping of {@link LocationVariable} to the {@link LocationVariable} which
     *        contains the initial value.
     * @param services The services instance.
     * @return The {@link Term} representing the initial updates.
     */
    protected Term buildUpdate(ImmutableList<ProgramVariable> paramVars,
            ImmutableList<LocationVariable> formalParamVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        Term update = null;
        for (Entry<LocationVariable, LocationVariable> atPreEntry : atPreVars.entrySet()) {
            final Term u = tb.elementary(atPreEntry.getValue(), tb.getBaseHeap());
            if (update == null) {
                update = u;
            } else {
                update = tb.parallel(update, u);
            }
        }
        if (isCopyOfMethodArgumentsUsed()) {
            Iterator<LocationVariable> formalParamIt = formalParamVars.iterator();
            Iterator<ProgramVariable> paramIt = paramVars.iterator();
            while (formalParamIt.hasNext()) {
                Term paramUpdate = tb.elementary(formalParamIt.next(), tb.var(paramIt.next()));
                update = tb.parallel(update, paramUpdate);
            }
        }
        return update;
    }

    /**
     * Checks if a copy of the method call arguments are used instead of the original method
     * arguments.
     *
     * @return {@code true} use copy of method call arguments, {@code false} use original method
     *         call arguments.
     */
    protected boolean isCopyOfMethodArgumentsUsed() {
        return true;
    }

    /**
     * Returns the name of the {@link Proof} based on the given transaction flag.
     *
     * @param transactionFlag The transaction flag.
     * @return The proof name to use.
     */
    protected abstract String buildPOName(boolean transactionFlag);

    private ImmutableList<LocationVariable> createFormalParamVars(
            final ImmutableList<ProgramVariable> paramVars, final Services proofServices) {
        // create arguments from formal parameters for method call
        ImmutableList<LocationVariable> formalParamVars = ImmutableSLList.nil();
        for (ProgramVariable paramVar : paramVars) {
            if (isCopyOfMethodArgumentsUsed()) {
                ProgramElementName pen = new ProgramElementName("_" + paramVar.name());
                LocationVariable formalParamVar =
                    new LocationVariable(pen, paramVar.getKeYJavaType());
                formalParamVars = formalParamVars.append(formalParamVar);
                register(formalParamVar, proofServices);
            } else {
                formalParamVars = formalParamVars.append((LocationVariable) paramVar);
                // The cast is ugly but legal. It is a bigger task to
                // refactor TB.paramVars to return a list of
                // LocationVariabe instead of ProgramVariable.
            }
        }
        return formalParamVars;
    }

    private ImmutableList<FunctionalOperationContract> collectLookupContracts(
            final IProgramMethod pm, final Services proofServices) {
        ImmutableList<FunctionalOperationContract> lookupContracts =
            ImmutableSLList.nil();
        ImmutableSet<FunctionalOperationContract> cs = proofServices.getSpecificationRepository()
                .getOperationContracts(getCalleeKeYJavaType(), pm);
        for (KeYJavaType superType : proofServices.getJavaInfo()
                .getAllSupertypes(getCalleeKeYJavaType())) {
            for (FunctionalOperationContract fop : cs) {
                if (fop.getSpecifiedIn().equals(superType)) {
                    lookupContracts = lookupContracts.append(fop);
                }
            }
        }
        return lookupContracts;
    }

    private Term getRepresentsFromContract(final IProgramMethod pm, final ProgramVariable selfVar,
            final ImmutableList<ProgramVariable> paramVars, final ProgramVariable resultVar,
            final List<LocationVariable> heaps,
            final Map<LocationVariable, LocationVariable> atPreVars, final Services proofServices) {
        ImmutableList<FunctionalOperationContract> lookupContracts =
            collectLookupContracts(pm, proofServices);
        Term representsFromContract = null;
        for (FunctionalOperationContract fop : lookupContracts) {
            representsFromContract = fop.getRepresentsAxiom(heaps.get(0), selfVar, paramVars,
                resultVar, atPreVars, proofServices);
            if (representsFromContract != null) {
                break;
            }
        }
        return representsFromContract;
    }

    private void register(final ImmutableList<ProgramVariable> paramVars,
            final ProgramVariable[] vars, final Collection<LocationVariable> atPreVars,
            final Services proofServices) {
        // register the variables so they are declared in proof header
        // if the proof is saved to a file
        register(paramVars, proofServices);
        for (ProgramVariable var : vars) {
            register(var, proofServices);
        }
        for (LocationVariable lv : atPreVars) {
            register(lv, proofServices);
        }
    }

    private Term createApplyGlobalUpdateTerm(final ProgramVariable selfVar,
            final ImmutableList<ProgramVariable> paramVars, final Term preImpliesProgPost,
            final Services proofServices) {
        final LocationVariable baseHeap = proofServices.getTypeConverter().getHeapLDT().getHeap();
        final Term selfVarTerm = selfVar == null ? null : tb.var(selfVar);
        final Term globalUpdate = getGlobalDefs(baseHeap, tb.getBaseHeap(), selfVarTerm,
            tb.var(paramVars), proofServices);
        final Term applyGlobalUpdate =
            globalUpdate == null ? preImpliesProgPost : tb.apply(globalUpdate, preImpliesProgPost);
        return applyGlobalUpdate;
    }

    private Term createPost(final ProgramVariable selfVar,
            final ImmutableList<ProgramVariable> paramVars,
            final ImmutableList<LocationVariable> formalParamVars, final ProgramVariable resultVar,
            final ProgramVariable exceptionVar, final List<LocationVariable> modHeaps,
            final Map<LocationVariable, LocationVariable> atPreVars,
            final List<LocationVariable> heaps, final Map<Term, Term> heapToBefore,
            final Services proofServices) {
        Term postTerm = getPost(modHeaps, selfVar, paramVars, resultVar, exceptionVar, atPreVars,
            proofServices);
        // Add uninterpreted predicate
        if (isAddUninterpretedPredicate()) {
            postTerm = tb.and(postTerm, ensureUninterpretedPredicateExists(paramVars,
                formalParamVars, exceptionVar, getUninterpretedPredicateName(), proofServices));
        }

        Term frameTerm = buildFrameClause(heaps, heapToBefore, selfVar, paramVars, proofServices);
        return tb.and(postTerm, frameTerm);
    }

    private Term createNonModelPOTerm(final IProgramMethod pm, final ProgramVariable selfVar,
            final ImmutableList<ProgramVariable> paramVars, final ProgramVariable resultVar,
            final ProgramVariable exceptionVar, final boolean transactionFlag,
            final List<LocationVariable> modHeaps,
            final Map<LocationVariable, LocationVariable> atPreVars, final Services proofServices) {
        final ImmutableList<LocationVariable> formalParamVars =
            createFormalParamVars(paramVars, proofServices);

        // build program block to execute in try clause
        // (must be done before pre condition is created).
        final ImmutableList<StatementBlock> sb =
            buildOperationBlocks(formalParamVars, selfVar, resultVar, proofServices);

        Term permsFor = createPermsFor(pm, modHeaps, proofServices, tb);
        // final Map<LocationVariable, Map<Term, Term>> heapToAtPre =
        // new LinkedHashMap<LocationVariable, Map<Term, Term>>();
        final Map<Term, Term> heapToAtPre = createHeapToAtPres(modHeaps, atPreVars, tb);

        // build precondition
        Term pre = tb.and(
            buildFreePre(selfVar, getCalleeKeYJavaType(), paramVars, modHeaps, proofServices),
            permsFor, getPre(modHeaps, selfVar, paramVars, atPreVars, proofServices));
        pre = addTransactionPrecondition(pre, transactionFlag, isTransactionApplicable(),
            proofServices, tb);
        // build program term
        Term post = createPost(selfVar, paramVars, formalParamVars, resultVar, exceptionVar,
            modHeaps, atPreVars, modHeaps, heapToAtPre, proofServices);
        post = modifyPostTerm(proofServices, post);

        final Term progPost = buildProgramTerm(paramVars, formalParamVars, selfVar, resultVar,
            exceptionVar, atPreVars, post, sb, proofServices);
        final Term preImpliesProgPost = tb.imp(pre, progPost);

        final Term applyGlobalUpdate =
            createApplyGlobalUpdateTerm(selfVar, paramVars, preImpliesProgPost, proofServices);
        return applyGlobalUpdate;
    }

    private Term createModelPOTerm(final IProgramMethod pm, final ProgramVariable selfVar,
            final ImmutableList<ProgramVariable> paramVars, final ProgramVariable resultVar,
            final List<LocationVariable> modHeaps,
            final Map<LocationVariable, LocationVariable> atPreVars, final Services proofServices) {
        final IObserverFunction target = javaInfo.getToplevelPM(getCalleeKeYJavaType(), pm);
        final ImmutableList<LocationVariable> formalParamVars =
            createFormalParamVars(paramVars, proofServices);

        final List<LocationVariable> heaps = addPreHeaps(target, modHeaps, atPreVars);
        final Map<LocationVariable, LocationVariable> atBeforeVars =
            HeapContext.getBeforeAtPreVars(heaps, proofServices, "Before");

        // build precondition
        Term permsFor = createPermsFor(pm, heaps, proofServices, tb);
        // final Map<LocationVariable, Map<Term, Term>> heapToAtPre =
        // new LinkedHashMap<LocationVariable, Map<Term, Term>>();
        final Map<Term, Term> heapToBefore = createHeapToAtPres(heaps, atBeforeVars, tb);

        Term pre =
            tb.and(buildFreePre(selfVar, getCalleeKeYJavaType(), paramVars, heaps, proofServices),
                permsFor, getPre(modHeaps, selfVar, paramVars, atPreVars, proofServices));
        // build program term
        final Term post = createPost(selfVar, paramVars, formalParamVars, resultVar, null, modHeaps,
            atPreVars, heaps, heapToBefore, proofServices);
        final Term representsFromContract = getRepresentsFromContract(pm, selfVar, paramVars,
            resultVar, heaps, atPreVars, proofServices);
        final Term saveBeforeHeaps = saveBeforeHeaps(heapToBefore, tb);

        final Term progPost = createProgPost(target, selfVar, paramVars, resultVar, modHeaps,
            atPreVars, saveBeforeHeaps, representsFromContract, post, tb);
        final Term poTerm = tb.imp(pre, progPost);
        return poTerm;
    }

    private boolean[] setTransactionFlags() {
        final boolean[] transactionFlags;
        if (isTransactionApplicable()) {
            transactionFlags = new boolean[] { false, true };
            poNames = new String[2];
        } else {
            transactionFlags = new boolean[] { false };
        }
        return transactionFlags;
    }
}
