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
import de.uka.ilkd.key.wd.WellDefinednessCheck;

import org.key_project.logic.Name;
import org.key_project.logic.op.Function;
import org.key_project.util.collection.ImmutableSet;
import org.key_project.util.java.ArrayUtil;

/**
 * A proof obligation for a {@link FunctionalBlockContract}.
 *
 * @author lanzinger
 */
public class FunctionalBlockContractPO extends AbstractPO implements ContractPO {

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
    private final FunctionalBlockContract contract;

    /**
     * The initial proof configuration.
     */
    private InitConfig proofConfig;

    /**
     *
     * @param initConfig the initial proof configuration.
     * @param contract the contract from which this PO is generated.
     */
    public FunctionalBlockContractPO(InitConfig initConfig, FunctionalBlockContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
    }

    /**
     *
     * @param localOutVariables a set of variables.
     * @param services services.
     * @param tb the TermBuilder to be used
     * @return an anonymizing update for the specified variables.
     */
    private static JTerm createLocalAnonUpdate(
            final ImmutableSet<LocationVariable> localOutVariables,
            final Services services, final TermBuilder tb) {
        JTerm localAnonUpdate = null;
        for (LocationVariable pv : localOutVariables) {
            final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
            final Function anonFunc = new JFunction(anonFuncName, pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final JTerm elemUpd = tb.elementary(pv, tb.func(anonFunc));
            if (localAnonUpdate == null) {
                localAnonUpdate = elemUpd;
            } else {
                localAnonUpdate = tb.parallel(localAnonUpdate, elemUpd);
            }
        }
        return localAnonUpdate;
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
        Map<LocationVariable, Function> anonHeaps =
            new LinkedHashMap<>(40);
        for (LocationVariable heap : heaps) {
            final String anonymisationName =
                tb.newName(AuxiliaryContractBuilders.ANON_IN_PREFIX + heap.name());
            final Function anonymisationFunction =
                new JFunction(new Name(anonymisationName), heap.sort(), true);
            services.getNamespaces().functions().addSafely(anonymisationFunction);
            anonHeaps.put(heap, anonymisationFunction);
        }
        return anonHeaps;
    }

    /**
     *
     * @param heaps heaps.
     * @param services services.
     * @param tb a term builder.
     * @return a map from every heap to an anonymization heap.
     */
    private static Map<LocationVariable, Function> createAnonOutHeaps(
            final List<LocationVariable> heaps, final FunctionalBlockContract contract,
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
     * @param variables the contract's variables.
     * @param heaps the heaps.
     * @param anonHeaps the anonymization heaps.
     * @param services services.
     * @return the updates.
     */
    private static JTerm[] createUpdates(final BlockContract.Variables variables,
            final List<LocationVariable> heaps, Map<LocationVariable, Function> anonHeaps,
            final Services services) {
        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final JTerm remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final JTerm outerRemembranceUpdate = updatesBuilder.buildOuterRemembranceUpdate();
        final JTerm anonInUpdate = updatesBuilder.buildAnonInUpdate(anonHeaps);
        return new JTerm[] { outerRemembranceUpdate, anonInUpdate, remembranceUpdate };
    }

    /**
     *
     * @param conditionsAndClausesBuilder a conditions and clauses builder.
     * @return the postconditions.
     */
    private static JTerm[] createPostconditions(
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder) {
        final Map<LocationVariable, JTerm> modifiableClauses =
            conditionsAndClausesBuilder.buildModifiableClauses();
        final Map<LocationVariable, JTerm> freeModifiableClauses =
            conditionsAndClausesBuilder.buildModifiableClauses();
        final JTerm postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final JTerm frameCondition =
            conditionsAndClausesBuilder.buildFrameCondition(
                modifiableClauses, freeModifiableClauses);
        return new JTerm[] { postcondition, frameCondition };
    }

    /**
     *
     * @param heaps the heaps.
     * @param anonHeaps the heaps used in the anonIn update.
     * @param anonOutHeaps the heaps used in the anonOut update.
     * @param localInVariables the free local variables in the block.
     * @param localOutVariables the free local variables modifiable by the block.
     * @param exceptionParameter the exception variable.
     * @param assumptions the preconditions.
     * @param postconditions the postconditions.
     * @param updates the update.
     * @param bc the contract being applied.
     * @param conditionsAndClausesBuilder a conditions and clauses builder.
     * @param configurator a goal configurator.
     * @param services services.
     * @param tb a term builder.
     * @return the validity formula for the contract.
     */
    private static JTerm setUpValidityTerm(final List<LocationVariable> heaps,
            Map<LocationVariable, Function> anonHeaps,
            Map<LocationVariable, Function> anonOutHeaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final ImmutableSet<LocationVariable> localOutVariables,
            final ProgramVariable exceptionParameter, final JTerm[] assumptions,
            final JTerm[] postconditions, final JTerm[] updates, final BlockContract bc,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final GoalsConfigurator configurator, final Services services, final TermBuilder tb) {
        JTerm validity = configurator.setUpValidityGoal(null, updates, assumptions, postconditions,
            exceptionParameter, conditionsAndClausesBuilder.getTerms());
        JTerm wellFormedAnonymisationHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedAnonymisationHeapsCondition(anonHeaps);
        validity = tb.imp(tb.and(assumptions[1], wellFormedAnonymisationHeapsCondition), validity);

        return addWdToValidityTerm(validity, updates, heaps, anonOutHeaps, localInVariables,
            localOutVariables, bc, configurator, services, tb);
    }

    /**
     *
     * @param validity the validity formula.
     * @param updates the updates.
     * @param heaps the heaps.
     * @param anonOutHeaps the heaps used in the anonOut update.
     * @param localInVariables the free local variables in the block.
     * @param localOutVariables the free local variables modifiable by the block.
     * @param bc the contract being applied.
     * @param configurator a goal configurator
     * @param services services.
     * @param tb a term builder.
     * @return the conjunction of the well-definedness formula and the validity formula.
     */
    private static JTerm addWdToValidityTerm(JTerm validity, final JTerm[] updates,
            final List<LocationVariable> heaps, Map<LocationVariable, Function> anonOutHeaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final ImmutableSet<LocationVariable> localOutVariables, final BlockContract bc,
            final GoalsConfigurator configurator, final Services services, final TermBuilder tb) {
        if (WellDefinednessCheck.isOn()) {
            final JTerm wdUpdate = services.getTermBuilder().parallel(updates[1], updates[2]);

            JTerm localAnonUpdate = createLocalAnonUpdate(localOutVariables, services, tb);

            if (localAnonUpdate == null) {
                localAnonUpdate = tb.skip();
            }

            JTerm wellDefinedness = configurator.setUpWdGoal(null, bc, wdUpdate, localAnonUpdate,
                heaps.get(0), anonOutHeaps.get(heaps.get(0)), localInVariables);

            validity = tb.and(wellDefinedness, validity);
        }
        return validity;
    }

    @Override
    public Configuration createLoaderConfig() {
        var c = super.createLoaderConfig();
        c.set("contract", contract.getName());
        return c;
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof FunctionalBlockContractPO other)) {
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
        if (!(obj instanceof FunctionalBlockContractPO other)) {
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
        final IProgramMethod pm = getProgramMethod();

        final StatementBlock block = getBlock();
        final LocationVariable selfVar = tb.selfVar(pm, getCalleeKeYJavaType(), makeNamesUnique);
        register(selfVar, services);
        final JTerm selfTerm = selfVar == null ? null : tb.var(selfVar);

        LoopContract innerLoopContract = contract.getAuxiliaryContract().toLoopContract();
        if (innerLoopContract != null) {
            services.getSpecificationRepository().addLoopContract(innerLoopContract
                    .replaceEnhancedForVariables(innerLoopContract.getBlock(), services),
                false);
        }

        final List<LocationVariable> heaps = HeapContext.getModifiableHeaps(services, false);
        final ImmutableSet<LocationVariable> localInVariables =
            MiscTools.getLocalIns(block, services);
        final ImmutableSet<LocationVariable> localOutVariables =
            MiscTools.getLocalOuts(block, services);

        Map<LocationVariable, Function> anonOutHeaps =
            createAnonOutHeaps(heaps, contract, services, tb);
        final BlockContract.Variables variables =
            new VariablesCreatorAndRegistrar(services, contract.getPlaceholderVariables())
                    .createAndRegister(selfTerm, false, contract.getBlock());
        final ProgramVariable exceptionParameter = KeYJavaASTFactory.localVariable(
            services.getVariableNamer().getTemporaryNameProposal("e"),
            variables.exception.getKeYJavaType());

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
            new ConditionsAndClausesBuilder(contract.getAuxiliaryContract(), heaps, variables,
                selfTerm, services);

        final JTerm[] assumptions = createAssumptions(pm, selfVar, heaps, localInVariables,
            conditionsAndClausesBuilder, services);
        final JTerm freePrecondition = conditionsAndClausesBuilder.buildFreePrecondition();

        final JTerm[] postconditions = createPostconditions(conditionsAndClausesBuilder);

        Map<LocationVariable, Function> anonHeaps = createAnonInHeaps(heaps, services, tb);

        final JTerm[] updates = createUpdates(variables, heaps, anonHeaps, services);

        final GoalsConfigurator configurator =
            setUpGoalConfigurator(block, selfVar, selfTerm, variables, services, tb);

        final JTerm validity = setUpValidityTerm(heaps, anonHeaps, anonOutHeaps, localInVariables,
            localOutVariables, exceptionParameter, ArrayUtil.add(assumptions, freePrecondition),
            postconditions, updates, contract.getAuxiliaryContract(), conditionsAndClausesBuilder,
            configurator, services, tb);
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
     *
     * @param block the block this contract belongs to.
     * @param selfVar the self variable.
     * @param selfTerm the self term.
     * @param variables the contract's variables.
     * @param services services.
     * @param tb a term builder.
     * @return a goal configurator.
     */
    private GoalsConfigurator setUpGoalConfigurator(final StatementBlock block,
            final ProgramVariable selfVar, final JTerm selfTerm,
            final BlockContract.Variables variables, final Services services,
            final TermBuilder tb) {
        final KeYJavaType kjt = getCalleeKeYJavaType();
        final TypeRef typeRef = new TypeRef(new ProgramElementName(kjt.getName()), 0, selfVar, kjt);
        final ExecutionContext ec = new ExecutionContext(typeRef, getProgramMethod(), selfVar);
        JModality.JavaModalityKind kind = contract.getModalityKind();
        JavaBlock jb = JavaBlock.createJavaBlock(new StatementBlock());
        final Instantiation inst =
            new Instantiation(tb.skip(), tb.tt(),
                JModality.getModality(kind, jb),
                selfTerm, block, ec);
        return new GoalsConfigurator(null, new TermLabelState(), inst,
            contract.getAuxiliaryContract().getLabels(), variables, null, services, null);
    }

    /**
     *
     * @param pm the method this contract belongs to.
     * @param selfVar the self variable.
     * @param heaps the heaps.
     * @param localInVariables the free local variables in the block.
     * @param conditionsAndClausesBuilder a conditions and clauses builder.
     * @param services services.
     * @return the preconditions.
     */
    private JTerm[] createAssumptions(final IProgramMethod pm, final LocationVariable selfVar,
            final List<LocationVariable> heaps,
            final ImmutableSet<LocationVariable> localInVariables,
            final ConditionsAndClausesBuilder conditionsAndClausesBuilder,
            final Services services) {
        final JTerm precondition = conditionsAndClausesBuilder.buildPrecondition();
        final JTerm wellFormedHeapsCondition =
            conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final JTerm reachableInCondition =
            conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);
        return new JTerm[] { precondition, wellFormedHeapsCondition, reachableInCondition,
            generateSelfNotNull(pm, selfVar), generateSelfCreated(heaps, pm, selfVar, services),
            generateSelfExactType(pm, selfVar, getCalleeKeYJavaType()) };
    }
}
