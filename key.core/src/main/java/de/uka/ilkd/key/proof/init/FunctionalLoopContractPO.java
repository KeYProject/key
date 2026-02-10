/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractAuxiliaryContractRule.Instantiation;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.speclang.*;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
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
    public static final Map<Boolean, String> TRANSACTION_TAGS =
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

    @Override
    public Configuration createLoaderConfig() {
        var c = super.createLoaderConfig();
        c.set("contract", contract.getName());
        return c;
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof FunctionalLoopContractPO other)) {
            return false;
        }
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
        if (!(obj instanceof FunctionalLoopContractPO other)) {
            return false;
        }
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
    public void readProblem() {
        assert proofConfig == null;
        final boolean makeNamesUnique = true;
        final Services services = postInit();
        final TermBuilder tb = services.getTermBuilder();
        final IProgramMethod pm = getProgramMethod();

        contract.replaceEnhancedForVariables(services);

        final LocationVariable selfVar = tb.selfVar(pm, getCalleeKeYJavaType(), makeNamesUnique);
        register(selfVar, services);
        final JTerm selfTerm = selfVar == null ? null : tb.var(selfVar);

        final List<LocationVariable> heaps = HeapContext.getModifiableHeaps(services, false);
        final Map<LocationVariable, Function> anonOutHeaps =
            createAnonOutHeaps(heaps, services, tb);

        final BlockContract.Variables variables =
            new VariablesCreatorAndRegistrar(services, contract.getPlaceholderVariables())
                    .createAndRegister(selfTerm, false, contract.getBlock());
        final LoopContract.Variables nextVariables =
            new VariablesCreatorAndRegistrar(services, variables)
                    .createAndRegisterCopies("_NEXT");

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
            new ConditionsAndClausesBuilder(contract.getAuxiliaryContract(), heaps, variables,
                selfTerm, services);

        final JTerm wellFormedHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final JTerm[] assumptions = createAssumptions(selfVar, heaps, wellFormedHeapsCondition,
            services, conditionsAndClausesBuilder);
        final JTerm freePrecondition = conditionsAndClausesBuilder.buildFreePrecondition();
        final Map<LocationVariable, JTerm> modifiableClauses =
            conditionsAndClausesBuilder.buildModifiableClauses();
        final Map<LocationVariable, JTerm> freeModifiableClauses =
            conditionsAndClausesBuilder.buildFreeModifiableClauses();
        final JTerm[] postconditionsNext =
            createPostconditionsNext(
                selfTerm, heaps, nextVariables, modifiableClauses, freeModifiableClauses, services);
        final JTerm[] postconditions =
            createPostconditions(modifiableClauses, freeModifiableClauses,
                conditionsAndClausesBuilder);
        final JTerm decreasesCheck = conditionsAndClausesBuilder.buildDecreasesCheck();

        final GoalsConfigurator configurator =
            createGoalConfigurator(selfVar, selfTerm, variables, services, tb);

        JTerm validity = setUpValidityGoal(selfTerm, heaps, anonOutHeaps, variables, nextVariables,
            modifiableClauses, freeModifiableClauses, ArrayUtil.add(assumptions, freePrecondition),
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
    public JTerm getMbyAtPre() {
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
     * @param modifiableClauses the contract's modifiable clauses.
     * @param freeModifiableClauses the loop's free modifiable clauses.
     * @param conditionsAndClausesBuilder a ConditionsAndClausesBuilder
     * @return the postconditions for the current loop iteration.
     */
    private JTerm[] createPostconditions(
            final Map<LocationVariable, JTerm> modifiableClauses,
            final Map<LocationVariable, JTerm> freeModifiableClauses,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final JTerm postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final JTerm frameCondition =
            conditionsAndClausesBuilder.buildFrameCondition(
                modifiableClauses, freeModifiableClauses);
        return new JTerm[] { postcondition, frameCondition };
    }

    /**
     * Creates postconditions for the next loop iteration.
     *
     * @param selfTerm the self term.
     * @param heaps the heaps.
     * @param nextVariables the variables for the next loop iteration.
     * @param modifiableClauses the modifiable clauses.
     * @param freeModifiableClauses the free modifiable clauses.
     * @param services services.
     * @return the postconditions for the next loop iteration.
     */
    private JTerm[] createPostconditionsNext(
            final JTerm selfTerm,
            final List<LocationVariable> heaps,
            final LoopContract.Variables nextVariables,
            final Map<LocationVariable, JTerm> modifiableClauses,
            final Map<LocationVariable, JTerm> freeModifiableClauses,
            final Services services) {
        final JTerm nextPostcondition =
            new ConditionsAndClausesBuilder(contract.getAuxiliaryContract(), heaps, nextVariables,
                selfTerm, services).buildPostcondition();
        final JTerm nextFrameCondition =
            new ConditionsAndClausesBuilder(contract.getAuxiliaryContract(), heaps, nextVariables,
                selfTerm, services).buildFrameCondition(modifiableClauses, freeModifiableClauses);
        return new JTerm[] { nextPostcondition, nextFrameCondition };
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
    private JTerm[] createAssumptions(final ProgramVariable selfVar,
            final List<LocationVariable> heaps, final JTerm wellFormedHeapsCondition,
            final Services services,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final IProgramMethod pm = getProgramMethod();
        final StatementBlock block = getBlock();
        final ImmutableSet<LocationVariable> localInVariables =
            MiscTools.getLocalIns(block, services);
        final JTerm precondition = conditionsAndClausesBuilder.buildPrecondition();
        final JTerm reachableInCondition =
            conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);

        return new JTerm[] { precondition, wellFormedHeapsCondition, reachableInCondition,
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
                new JFunction(new Name(anonymisationName), heap.sort(), true);
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
    private Map<LocationVariable, Function> createAnonOutHeaps(
            final List<LocationVariable> heaps,
            final Services services, final TermBuilder tb) {
        Map<LocationVariable, Function> anonOutHeaps =
            new LinkedHashMap<>(40);
        for (LocationVariable heap : heaps) {
            if (contract.hasModifiableClause(heap)) {
                final String anonymisationName =
                    tb.newName(AuxiliaryContractBuilders.ANON_OUT_PREFIX + heap.name());
                final Function anonymisationFunction =
                    new JFunction(new Name(anonymisationName), heap.sort(), true);
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
            final JTerm selfTerm, final BlockContract.Variables variables, final Services services,
            final TermBuilder tb) {
        final TermLabelState termLabelState = new TermLabelState();
        final KeYJavaType kjt = getCalleeKeYJavaType();
        final TypeRef ref = new TypeRef(new ProgramElementName(kjt.getName()), 0, selfVar, kjt);
        final ExecutionContext ec = new ExecutionContext(ref, getProgramMethod(), selfVar);

        // TODO (DD): HACK
        JModality.JavaModalityKind kind = contract.getModalityKind();
        JavaBlock jb = JavaBlock.createJavaBlock(new StatementBlock());
        final Instantiation inst =
            new Instantiation(tb.skip(), tb.tt(), JModality.getModality(kind, jb),
                selfTerm, getBlock(), ec);

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
     * @param modifiableClauses the modifiable clauses.
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
    private JTerm setUpValidityGoal(final JTerm selfTerm, final List<LocationVariable> heaps,
            final Map<LocationVariable, Function> anonOutHeaps,
            final BlockContract.Variables variables, final LoopContract.Variables nextVariables,
            final Map<LocationVariable, JTerm> modifiableClauses,
            final Map<LocationVariable, JTerm> freeModifiableClauses, final JTerm[] assumptions,
            final JTerm decreasesCheck, final JTerm[] postconditions,
            final JTerm[] postconditionsNext,
            final JTerm wellFormedHeapsCondition, final GoalsConfigurator configurator,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder, final Services services,
            final TermBuilder tb) {
        final LocationVariable exceptionParameter = KeYJavaASTFactory.localVariable(
            services.getVariableNamer().getTemporaryNameProposal("e"),
            variables.exception.getKeYJavaType());

        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final JTerm remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final JTerm outerRemembranceUpdate = updatesBuilder.buildOuterRemembranceUpdate();
        final JTerm nextRemembranceUpdate =
            new UpdatesBuilder(nextVariables, services).buildRemembranceUpdate(heaps);

        Map<LocationVariable, Function> anonInHeaps = createAnonInHeaps(heaps, services, tb);

        final JTerm anonInUpdate = updatesBuilder.buildAnonInUpdate(anonInHeaps);
        final JTerm context = tb.sequential(outerRemembranceUpdate, anonInUpdate);

        JTerm validity = configurator.setUpLoopValidityGoal(null, contract.getAuxiliaryContract(),
            context, remembranceUpdate, nextRemembranceUpdate, anonOutHeaps, modifiableClauses,
            freeModifiableClauses, assumptions, decreasesCheck, postconditions, postconditionsNext,
            exceptionParameter, variables.termify(selfTerm), nextVariables);

        JTerm wellFormedAnonymisationHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedAnonymisationHeapsCondition(anonInHeaps);
        return tb.imp(tb.and(wellFormedHeapsCondition, wellFormedAnonymisationHeapsCondition),
            validity);
    }
}
