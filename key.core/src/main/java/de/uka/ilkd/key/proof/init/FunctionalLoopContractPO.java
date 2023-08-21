/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractRule.Instantiation;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.ArrayUtil;

/**
 * A proof obligation for a {@link FunctionalLoopContract}.
 *
 * @author lanzinger
 */
public class FunctionalLoopContractPO extends AbstractPO implements ContractPO {

    /**
     * Transaction tags.
     */
    private static final Map<Boolean, String> TRANSACTION_TAGS =
        new LinkedHashMap<>();

    static {
        TRANSACTION_TAGS.put(false, "transaction_inactive");
        TRANSACTION_TAGS.put(true, "transaction_active");
    }

    /**
     * The contract from which this PO is generated.
     */
    private final FunctionalLoopContract contract;

    /**
     * The initial proof configuration.
     */
    private InitConfig proofConfig;

    /**
     *
     * @param initConfig the initial proof configuration.
     * @param contract the contract from which this PO is generated.
     */
    public FunctionalLoopContractPO(InitConfig initConfig, FunctionalLoopContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
    }

    /**
     * Instantiates a new proof obligation with the given settings.
     *
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     * @throws IOException Occurred Exception.
     */
    public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties)
            throws IOException {
        String contractName = properties.getProperty("contract");
        int proofNum = 0;
        String baseContractName = null;
        int ind = -1;
        for (String tag : FunctionalLoopContractPO.TRANSACTION_TAGS.values()) {
            ind = contractName.indexOf("." + tag);
            if (ind > 0) {
                break;
            }
            proofNum++;
        }
        if (ind == -1) {
            baseContractName = contractName;
            proofNum = 0;
        } else {
            baseContractName = contractName.substring(0, ind);
        }
        final Contract contract = initConfig.getServices().getSpecificationRepository()
                .getContractByName(baseContractName);
        if (contract == null) {
            throw new RuntimeException("Contract not found: " + baseContractName);
        } else {
            ProofOblInput po = contract.createProofObl(initConfig);
            return new LoadedPOContainer(po, proofNum);
        }
    }

    @Override
    public void fillSaveProperties(Properties properties) {
        super.fillSaveProperties(properties);
        properties.setProperty("contract", contract.getName());
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof FunctionalLoopContractPO)) {
            return false;
        }

        FunctionalLoopContractPO other = (FunctionalLoopContractPO) po;
        return contract.equals(other.contract);
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((contract == null) ? 0 : contract.hashCode());
        result = prime * result + ((environmentConfig == null) ? 0 : environmentConfig.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof FunctionalLoopContractPO)) {
            return false;
        }
        FunctionalLoopContractPO other = (FunctionalLoopContractPO) obj;
        if (contract == null) {
            if (other.contract != null) {
                return false;
            }
        } else if (!contract.equals(other.contract)) {
            return false;
        }
        if (environmentConfig == null) {
            return other.environmentConfig == null;
        } else {
            return environmentConfig.equals(other.environmentConfig);
        }
    }

    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;
        final boolean makeNamesUnique = true;
        final Services services = postInit();
        final TermBuilder tb = services.getTermBuilder();
        final IProgramMethod pm = getProgramMethod();

        contract.replaceEnhancedForVariables(services);

        final ProgramVariable selfVar = tb.selfVar(pm, getCalleeKeYJavaType(), makeNamesUnique);
        register(selfVar, services);
        final Term selfTerm = selfVar == null ? null : tb.var(selfVar);

        final List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        final Map<LocationVariable, Function> anonOutHeaps =
            createAnonOutHeaps(heaps, services, tb);

        final BlockContract.Variables variables =
            new VariablesCreatorAndRegistrar(null, contract.getPlaceholderVariables(), services)
                    .createAndRegister(selfTerm, false, contract.getBlock());
        final LoopContract.Variables nextVariables =
            new VariablesCreatorAndRegistrar(null, variables, services)
                    .createAndRegisterCopies("_NEXT");

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
            new ConditionsAndClausesBuilder(contract.getAuxiliaryContract(), heaps, variables,
                selfTerm, services);

        final Term wellFormedHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final Term[] assumptions = createAssumptions(selfVar, heaps, wellFormedHeapsCondition,
            services, conditionsAndClausesBuilder);
        final Term freePrecondition = conditionsAndClausesBuilder.buildFreePrecondition();
        final Map<LocationVariable, Term> modifiesClauses =
            conditionsAndClausesBuilder.buildModifiesClauses();
        final Map<LocationVariable, Term> freeModifiesClauses =
            conditionsAndClausesBuilder.buildFreeModifiesClauses();
        final Term[] postconditionsNext =
            createPostconditionsNext(
                selfTerm, heaps, nextVariables, modifiesClauses, freeModifiesClauses, services);
        final Term[] postconditions =
            createPostconditions(modifiesClauses, freeModifiesClauses, conditionsAndClausesBuilder);
        final Term decreasesCheck = conditionsAndClausesBuilder.buildDecreasesCheck();

        final GoalsConfigurator configurator =
            createGoalConfigurator(selfVar, selfTerm, variables, services, tb);

        Term validity = setUpValidityGoal(selfTerm, heaps, anonOutHeaps, variables, nextVariables,
            modifiesClauses, freeModifiesClauses, ArrayUtil.add(assumptions, freePrecondition),
            decreasesCheck, postconditions, postconditionsNext, wellFormedHeapsCondition,
            configurator, conditionsAndClausesBuilder, services, tb);

        assignPOTerms(validity);
        collectClassAxioms(getCalleeKeYJavaType(), proofConfig);
        generateWdTaclets(proofConfig);
    }

    /**
     *
     * @return the contract's block.
     * @see AuxiliaryContract#getBlock()
     */
    public StatementBlock getBlock() {
        return contract.getBlock();
    }

    /**
     *
     * @return the type containing this contract.
     * @see SpecificationElement#getKJT()
     */
    public KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
    }

    /**
     *
     * @return the method containing this contract.
     * @see AuxiliaryContract#getMethod()
     */
    public IProgramMethod getProgramMethod() {
        return contract.getMethod();
    }

    @Override
    public Contract getContract() {
        return contract;
    }

    @Override
    public Term getMbyAtPre() {
        throw new UnsupportedOperationException();
    }

    /**
     * Initializes the proof configuration.
     *
     * @return the services from the proof configuration.
     */
    protected Services postInit() {
        proofConfig = environmentConfig.deepCopy();
        final Services proofServices = proofConfig.getServices();
        tb = proofServices.getTermBuilder();
        return proofServices;
    }

    @Override
    protected InitConfig getCreatedInitConfigForSingleProof() {
        return proofConfig;
    }

    /**
     * Creates postconditions for the current loop iteration.
     *
     * @param modifiesClauses the contract's modifies clauses.
     * @param freeModifiesClauses the loop's free modifies clauses.
     * @param conditionsAndClausesBuilder a ConditionsAndClausesBuilder
     * @return the postconditions for the current loop iteration.
     */
    private Term[] createPostconditions(
            final Map<LocationVariable, Term> modifiesClauses,
            final Map<LocationVariable, Term> freeModifiesClauses,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final Term postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final Term frameCondition =
            conditionsAndClausesBuilder.buildFrameCondition(
                modifiesClauses, freeModifiesClauses);
        return new Term[] { postcondition, frameCondition };
    }

    /**
     * Creates postconditions for the next loop iteration.
     *
     * @param selfTerm the self term.
     * @param heaps the heaps.
     * @param nextVariables the variables for the next loop iteration.
     * @param modifiesClauses the modified clauses.
     * @param freeModifiesClauses the free modified clauses.
     * @param services services.
     * @return the postconditions for the next loop iteration.
     */
    private Term[] createPostconditionsNext(
            final Term selfTerm,
            final List<LocationVariable> heaps,
            final LoopContract.Variables nextVariables,
            final Map<LocationVariable, Term> modifiesClauses,
            final Map<LocationVariable, Term> freeModifiesClauses,
            final Services services) {
        final Term nextPostcondition =
            new ConditionsAndClausesBuilder(contract.getAuxiliaryContract(), heaps, nextVariables,
                selfTerm, services).buildPostcondition();
        final Term nextFrameCondition =
            new ConditionsAndClausesBuilder(contract.getAuxiliaryContract(), heaps, nextVariables,
                selfTerm, services).buildFrameCondition(modifiesClauses, freeModifiesClauses);
        return new Term[] { nextPostcondition, nextFrameCondition };
    }

    /**
     *
     * @param selfVar the self variable.
     * @param heaps the heaps.
     * @param wellFormedHeapsCondition the condition that all heaps are well-formed.
     * @param services services.
     * @param conditionsAndClausesBuilder a conditions and clauses builder.
     * @return the preconditions.
     */
    private Term[] createAssumptions(final ProgramVariable selfVar,
            final List<LocationVariable> heaps, final Term wellFormedHeapsCondition,
            final Services services,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final IProgramMethod pm = getProgramMethod();
        final StatementBlock block = getBlock();
        final ImmutableSet<ProgramVariable> localInVariables =
            MiscTools.getLocalIns(block, services);
        final Term precondition = conditionsAndClausesBuilder.buildPrecondition();
        final Term reachableInCondition =
            conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);

        return new Term[] { precondition, wellFormedHeapsCondition, reachableInCondition,
            generateSelfNotNull(pm, selfVar), generateSelfCreated(heaps, pm, selfVar, services),
            generateSelfExactType(pm, selfVar, getCalleeKeYJavaType()) };
    }

    /**
     *
     * @param heaps heaps.
     * @param services services.
     * @param tb a term builder.
     * @return a map from every heap to an anonymization heap.
     */
    private static Map<LocationVariable, Function> createAnonInHeaps(
            final List<LocationVariable> heaps, final Services services, final TermBuilder tb) {
        Map<LocationVariable, Function> anonInHeaps =
            new LinkedHashMap<>(40);

        for (LocationVariable heap : heaps) {
            final String anonymisationName =
                tb.newName(AuxiliaryContractBuilders.ANON_IN_PREFIX + heap.name());
            final Function anonymisationFunction =
                new Function(new Name(anonymisationName), heap.sort(), true);
            services.getNamespaces().functions().addSafely(anonymisationFunction);
            anonInHeaps.put(heap, anonymisationFunction);
        }
        return anonInHeaps;
    }

    /**
     *
     * @param heaps heaps.
     * @param services services.
     * @param tb a term builder.
     * @return a map from every heap to an anonymization heap.
     */
    private Map<LocationVariable, Function> createAnonOutHeaps(final List<LocationVariable> heaps,
            final Services services, final TermBuilder tb) {
        Map<LocationVariable, Function> anonOutHeaps =
            new LinkedHashMap<>(40);
        for (LocationVariable heap : heaps) {
            if (contract.hasModifiesClause(heap)) {
                final String anonymisationName =
                    tb.newName(AuxiliaryContractBuilders.ANON_OUT_PREFIX + heap.name());
                final Function anonymisationFunction =
                    new Function(new Name(anonymisationName), heap.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                anonOutHeaps.put(heap, anonymisationFunction);
            }
        }
        return anonOutHeaps;
    }

    /**
     *
     * @param selfVar the self variable.
     * @param selfTerm the self term.
     * @param variables the contract's variables.
     * @param services services.
     * @param tb a term builder.
     * @return a goal configurator.
     */
    private GoalsConfigurator createGoalConfigurator(final ProgramVariable selfVar,
            final Term selfTerm, final BlockContract.Variables variables, final Services services,
            final TermBuilder tb) {
        final TermLabelState termLabelState = new TermLabelState();
        final KeYJavaType kjt = getCalleeKeYJavaType();
        final TypeRef ref = new TypeRef(new ProgramElementName(kjt.getName()), 0, selfVar, kjt);
        final ExecutionContext ec = new ExecutionContext(ref, getProgramMethod(), selfVar);

        final Instantiation inst =
            new Instantiation(tb.skip(), tb.tt(), contract.getModality(), selfTerm, getBlock(), ec);

        return new GoalsConfigurator(null, termLabelState, inst,
            contract.getAuxiliaryContract().getLabels(), variables, null, services, null);
    }

    /**
     *
     * @param selfTerm the self term
     * @param heaps the heaps.
     * @param anonOutHeaps the heaps used in the anonOut update.
     * @param variables the contract's variables.
     * @param nextVariables the variables for the next loop iteration.
     * @param modifiesClauses the modified clauses.
     * @param assumptions the preconditions.
     * @param decreasesCheck the decreases check.
     * @param postconditions the postconditions for the current loop iteration.
     * @param postconditionsNext the postconditions for the next loop iteration.
     * @param wellFormedHeapsCondition the condition that all heaps are well-formed.
     * @param configurator a goal configurator.
     * @param conditionsAndClausesBuilder a conditions and clauses builder.
     * @param services services.
     * @param tb a term builder.
     * @return the validity formula for the contract.
     */
    private Term setUpValidityGoal(final Term selfTerm, final List<LocationVariable> heaps,
            final Map<LocationVariable, Function> anonOutHeaps,
            final BlockContract.Variables variables, final LoopContract.Variables nextVariables,
            final Map<LocationVariable, Term> modifiesClauses,
            final Map<LocationVariable, Term> freeModifiesClauses, final Term[] assumptions,
            final Term decreasesCheck, final Term[] postconditions, final Term[] postconditionsNext,
            final Term wellFormedHeapsCondition, final GoalsConfigurator configurator,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder, final Services services,
            final TermBuilder tb) {
        final ProgramVariable exceptionParameter = KeYJavaASTFactory.localVariable(
            services.getVariableNamer().getTemporaryNameProposal("e"),
            variables.exception.getKeYJavaType());

        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term outerRemembranceUpdate = updatesBuilder.buildOuterRemembranceUpdate();
        final Term nextRemembranceUpdate =
            new UpdatesBuilder(nextVariables, services).buildRemembranceUpdate(heaps);

        Map<LocationVariable, Function> anonInHeaps = createAnonInHeaps(heaps, services, tb);

        final Term anonInUpdate = updatesBuilder.buildAnonInUpdate(anonInHeaps);
        final Term context = tb.sequential(outerRemembranceUpdate, anonInUpdate);

        Term validity = configurator.setUpLoopValidityGoal(null, contract.getAuxiliaryContract(),
            context, remembranceUpdate, nextRemembranceUpdate, anonOutHeaps, modifiesClauses,
            freeModifiesClauses, assumptions, decreasesCheck, postconditions, postconditionsNext,
            exceptionParameter, variables.termify(selfTerm), nextVariables);

        Term wellFormedAnonymisationHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedAnonymisationHeapsCondition(anonInHeaps);
        return tb.imp(tb.and(wellFormedHeapsCondition, wellFormedAnonymisationHeapsCondition),
            validity);
    }
}
