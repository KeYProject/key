package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import org.key_project.util.collection.ImmutableSet;

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
import de.uka.ilkd.key.rule.AbstractBlockSpecificationElementRule.Instantiation;
import de.uka.ilkd.key.rule.BlockContractBuilders;
import de.uka.ilkd.key.rule.BlockContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.GoalsConfigurator;
import de.uka.ilkd.key.rule.BlockContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalLoopContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.util.MiscTools;

/**
 * A proof obligation for a {@link FunctionalLoopContract}.
 */
public class FunctionalLoopContractPO extends AbstractPO implements ContractPO {

    private static final Map<Boolean, String> TRANSACTION_TAGS =
            new LinkedHashMap<Boolean, String>();

    private FunctionalLoopContract contract;
    private InitConfig proofConfig;

    public FunctionalLoopContractPO(InitConfig initConfig,
                                    FunctionalLoopContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
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
        final Contract contract =
                initConfig.getServices().getSpecificationRepository()
                .getContractByName(baseContractName);
        if (contract == null) {
            throw new RuntimeException("Contract not found: " + baseContractName);
        } else {
            ProofOblInput po = contract.createProofObl(initConfig);
            return new LoadedPOContainer(po, proofNum);
        }
    }

    private static Map<LocationVariable, Function>
                createAnonHeaps(final List<LocationVariable> heaps,
                                final Services services,
                                final TermBuilder tb) {
        Map<LocationVariable, Function> anonInHeaps =
                new LinkedHashMap<LocationVariable, Function>(40);

        for (LocationVariable heap : heaps) {
            final String anonymisationName =
                    tb.newName(BlockContractBuilders.ANON_IN_PREFIX + heap.name());
            final Function anonymisationFunction =
                    new Function(new Name(anonymisationName), heap.sort(), true);
            services.getNamespaces().functions().addSafely(anonymisationFunction);
            anonInHeaps.put(heap, anonymisationFunction);
        }
        return anonInHeaps;
    }

    static {
        TRANSACTION_TAGS.put(false, "transaction_inactive");
        TRANSACTION_TAGS.put(true, "transaction_active");
    }

    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
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
        result = prime * result
                + ((contract == null) ? 0 : contract.hashCode());
        result = prime * result
                + ((environmentConfig == null) ?
                        0 : environmentConfig.hashCode());
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
            if (other.environmentConfig != null) {
                return false;
            }
        } else if (!environmentConfig.equals(other.environmentConfig)) {
            return false;
        }
        return true;
    }

    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;
        final boolean makeNamesUnique = true;
        final Services services = postInit();
        final TermBuilder tb = services.getTermBuilder();
        final IProgramMethod pm = getProgramMethod();

        final ProgramVariable selfVar =
                tb.selfVar(pm, getCalleeKeYJavaType(), makeNamesUnique);
        register(selfVar, services);
        final Term selfTerm = selfVar == null ? null : tb.var(selfVar);

        final List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        final Map<LocationVariable, Function> anonOutHeaps =
                createAnonOutHeaps(heaps, services, tb);

        final BlockContract.Variables variables = new VariablesCreatorAndRegistrar(
                null, contract.getPlaceholderVariables(), services
                ).createAndRegister(selfTerm, false);
        final LoopContract.Variables nextVariables = new VariablesCreatorAndRegistrar(
                null, variables, services).createAndRegisterCopies("_NEXT");

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
                new ConditionsAndClausesBuilder(contract.getLoopContract(),
                                                heaps, variables, selfTerm,
                                                services);

        final Term wellFormedHeapsCondition =
                conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final Term[] assumptions =
                createAssumptions(selfVar, heaps, wellFormedHeapsCondition,
                                  services, conditionsAndClausesBuilder);
        final Map<LocationVariable, Term> modifiesClauses =
                conditionsAndClausesBuilder.buildModifiesClauses();
        final Term[] postconditionsNext =
                createPostconditionsNext(selfTerm, heaps, nextVariables,
                                         modifiesClauses, services);
        final Term[] postconditions =
                createPostconditions(modifiesClauses, conditionsAndClausesBuilder);
        final Term decreasesCheck =
                conditionsAndClausesBuilder.buildDecreasesCheck();

        final GoalsConfigurator configurator =
                createGoalConfigurator(selfVar, selfTerm, variables, services, tb);

        Term validity =
                setUpValidityGoal(selfTerm, heaps, anonOutHeaps,
                                  variables, nextVariables, modifiesClauses,
                                  assumptions, decreasesCheck, postconditions,
                                  postconditionsNext, wellFormedHeapsCondition,
                                  configurator, conditionsAndClausesBuilder,
                                  services, tb);

        assignPOTerms(validity);
        collectClassAxioms(getCalleeKeYJavaType(), proofConfig);
        generateWdTaclets(proofConfig);
    }

    public StatementBlock getBlock() {
        return contract.getBlock();
    }

    public KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
    }

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


    private Term[] createPostconditions(final Map<LocationVariable, Term>
                                                modifiesClauses,
                                        final ConditionsAndClausesBuilder
                                                conditionsAndClausesBuilder) {
        final Term postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final Term frameCondition =
                conditionsAndClausesBuilder.buildFrameCondition(modifiesClauses);
        return new Term[] { postcondition, frameCondition };
    }

    private Term[] createPostconditionsNext(final Term selfTerm,
                                            final List<LocationVariable> heaps,
                                            final LoopContract.Variables nextVariables,
                                            final Map<LocationVariable, Term> modifiesClauses,
                                            final Services services) {
        final Term nextPostcondition =
                new ConditionsAndClausesBuilder(contract.getLoopContract(),
                                                heaps, nextVariables,
                                                selfTerm, services)
                    .buildPostcondition();
        final Term nextFrameCondition =
                new ConditionsAndClausesBuilder(contract.getLoopContract(),
                                                heaps, nextVariables,
                                                selfTerm, services)
                    .buildFrameCondition(modifiesClauses);
        return new Term[] { nextPostcondition, nextFrameCondition };
    }

    private Term[] createAssumptions(final ProgramVariable selfVar,
                                     final List<LocationVariable> heaps,
                                     final Term wellFormedHeapsCondition,
                                     final Services services,
                                     final ConditionsAndClausesBuilder
                                             conditionsAndClausesBuilder) {
        final IProgramMethod pm = getProgramMethod();
        final StatementBlock block = getBlock();
        final ImmutableSet<ProgramVariable> localInVariables =
                MiscTools.getLocalIns(block, services);
        final Term precondition = conditionsAndClausesBuilder.buildPrecondition();
        final Term reachableInCondition =
                conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);

        return new Term[] { precondition, wellFormedHeapsCondition,
                            reachableInCondition,
                            generateSelfNotNull(pm, selfVar),
                            generateSelfCreated(heaps, pm, selfVar, services),
                            generateSelfExactType(pm, selfVar,
                                                  getCalleeKeYJavaType()) };
    }

    private Map<LocationVariable, Function>
                createAnonOutHeaps(final List<LocationVariable> heaps,
                                   final Services services,
                                   final TermBuilder tb) {
        Map<LocationVariable, Function> anonOutHeaps =
                new LinkedHashMap<LocationVariable, Function>(40);
        for (LocationVariable heap : heaps) {
            if(contract.hasModifiesClause(heap)) {
                final String anonymisationName =
                        tb.newName(BlockContractBuilders.ANON_OUT_PREFIX + heap.name());
                final Function anonymisationFunction =
                        new Function(new Name(anonymisationName), heap.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                anonOutHeaps.put(heap, anonymisationFunction);
            }
        }
        return anonOutHeaps;
    }

    private GoalsConfigurator
                createGoalConfigurator(final ProgramVariable selfVar,
                                       final Term selfTerm,
                                       final BlockContract.Variables variables,
                                       final Services services,
                                       final TermBuilder tb) {
        final TermLabelState termLabelState = new TermLabelState();
        final KeYJavaType kjt = getCalleeKeYJavaType();
        final TypeRef ref = new TypeRef(new ProgramElementName(kjt.getName()),
                                        0, selfVar, kjt);
        final ExecutionContext ec =
                new ExecutionContext(ref, getProgramMethod(), selfVar);

        final Instantiation inst =
                new Instantiation(tb.skip(), tb.tt(), contract.getModality(),
                                  selfTerm, getBlock(), ec);

        return new GoalsConfigurator(null, termLabelState, inst,
                                     contract.getLoopContract().getLabels(),
                                     variables, null, services, null);
    }

    private Term setUpValidityGoal(final Term selfTerm,
                                   final List<LocationVariable> heaps,
                                   final Map<LocationVariable, Function> anonOutHeaps,
                                   final BlockContract.Variables variables,
                                   final LoopContract.Variables nextVariables,
                                   final Map<LocationVariable, Term> modifiesClauses,
                                   final Term[] assumptions,
                                   final Term decreasesCheck,
                                   final Term[] postconditions,
                                   final Term[] postconditionsNext,
                                   final Term wellFormedHeapsCondition,
                                   final GoalsConfigurator configurator,
                                   final ConditionsAndClausesBuilder
                                           conditionsAndClausesBuilder,
                                   final Services services,
                                   final TermBuilder tb) {
        final ProgramVariable exceptionParameter =
                KeYJavaASTFactory.localVariable(services.getVariableNamer()
                        .getTemporaryNameProposal("e"), variables.exception.getKeYJavaType());

        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term outerRemembranceUpdate = updatesBuilder.buildOuterRemembranceUpdate();
        final Term nextRemembranceUpdate =
                new UpdatesBuilder(nextVariables, services).buildRemembranceUpdate(heaps);

        Map<LocationVariable, Function> anonInHeaps = createAnonHeaps(heaps, services, tb);

        final Term anonInUpdate = updatesBuilder.buildAnonInUpdate(anonInHeaps);
        final Term context = tb.sequential(outerRemembranceUpdate, anonInUpdate);

        Term validity =
                configurator.setUpLoopValidityGoal(null,
                                                   contract.getLoopContract(),
                                                   context,
                                                   remembranceUpdate,
                                                   nextRemembranceUpdate,
                                                   anonOutHeaps,
                                                   modifiesClauses,
                                                   assumptions,
                                                   decreasesCheck,
                                                   postconditions,
                                                   postconditionsNext,
                                                   exceptionParameter,
                                                   variables.termify(selfTerm),
                                                   nextVariables);

        Term wellFormedAnonymisationHeapsCondition =
                conditionsAndClausesBuilder
                    .buildWellFormedAnonymisationHeapsCondition(anonInHeaps);
        return tb.imp(tb.and(wellFormedHeapsCondition,
                             wellFormedAnonymisationHeapsCondition),
                      validity);
    }
}
