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
import de.uka.ilkd.key.speclang.FunctionalBlockContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.speclang.WellDefinednessCheck;
import de.uka.ilkd.key.util.MiscTools;

/**
 * A proof obligation for a {@link FunctionalBlockContract}.
 */
public class FunctionalBlockContractPO extends AbstractPO implements ContractPO {

    private static final Map<Boolean, String> TRANSACTION_TAGS =
            new LinkedHashMap<Boolean, String>();

    static {
        TRANSACTION_TAGS.put(false, "transaction_inactive");
        TRANSACTION_TAGS.put(true, "transaction_active");
    }

    private FunctionalBlockContract contract;
    private InitConfig proofConfig;

    public FunctionalBlockContractPO(InitConfig initConfig,
            FunctionalBlockContract contract) {
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
        for (String tag : FunctionalBlockContractPO.TRANSACTION_TAGS.values()) {
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

    private static Term
        createLocalAnonUpdate(final ImmutableSet<ProgramVariable> localOutVariables,
                              final Services services, final TermBuilder tb) {
        Term localAnonUpdate = null;
        for(ProgramVariable pv : localOutVariables) {
            final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
            final Function anonFunc = new Function(anonFuncName, pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final Term elemUpd = tb.elementary((LocationVariable)pv, tb.func(anonFunc));
            if(localAnonUpdate == null) {
                localAnonUpdate = elemUpd;
            } else {
                localAnonUpdate = tb.parallel(localAnonUpdate, elemUpd);
            }
        }
        return localAnonUpdate;
    }

    private static Map<LocationVariable, Function>
        createAnonHeaps(final List<LocationVariable> heaps,
                        final Services services,
                        final TermBuilder tb) {
        Map<LocationVariable, Function> anonHeaps =
                new LinkedHashMap<LocationVariable, Function>(40);
        for (LocationVariable heap : heaps) {
            final String anonymisationName =
                    tb.newName(BlockContractBuilders.ANON_IN_PREFIX + heap.name());
            final Function anonymisationFunction =
                    new Function(new Name(anonymisationName), heap.sort(), true);
            services.getNamespaces().functions().addSafely(anonymisationFunction);
            anonHeaps.put(heap, anonymisationFunction);
        }
        return anonHeaps;
    }


    private static Map<LocationVariable, Function>
                createAnonOutHeaps(final List<LocationVariable> heaps,
                                   final FunctionalBlockContract contract,
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

    private static Term[] createUpdates(final BlockContract.Variables variables,
                                        final List<LocationVariable> heaps,
                                        Map<LocationVariable, Function> anonHeaps,
                                        final Services services) {
        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term outerRemembranceUpdate = updatesBuilder.buildOuterRemembranceUpdate();
        final Term anonInUpdate = updatesBuilder.buildAnonInUpdate(anonHeaps);
        return new Term[] { outerRemembranceUpdate, anonInUpdate, remembranceUpdate };
    }

    private static Term[]
                createPostconditions(final ConditionsAndClausesBuilder
                                                conditionsAndClausesBuilder) {
        final Map<LocationVariable, Term> modifiesClauses =
                conditionsAndClausesBuilder.buildModifiesClauses();
        final Term postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final Term frameCondition =
                conditionsAndClausesBuilder.buildFrameCondition(modifiesClauses);
        return new Term[] { postcondition, frameCondition };
    }

    private static Term setUpValidityTerm(final List<LocationVariable> heaps,
                                          Map<LocationVariable, Function> anonHeaps,
                                          Map<LocationVariable, Function> anonOutHeaps,
                                          final ImmutableSet<ProgramVariable> localInVariables,
                                          final ImmutableSet<ProgramVariable> localOutVariables,
                                          final ProgramVariable exceptionParameter,
                                          final Term[] assumptions,
                                          final Term[] postconditions,
                                          final Term[] updates,
                                          final BlockContract bc,
                                          final ConditionsAndClausesBuilder
                                                      conditionsAndClausesBuilder,
                                          final GoalsConfigurator configurator,
                                          final Services services,
                                          final TermBuilder tb) {
        Term validity = configurator.setUpValidityGoal(null, updates, assumptions,
                                                       postconditions,
                                                       exceptionParameter,
                                                       conditionsAndClausesBuilder.getTerms());
        Term wellFormedAnonymisationHeapsCondition =
                conditionsAndClausesBuilder.buildWellFormedAnonymisationHeapsCondition(anonHeaps);
        validity = tb.imp(tb.and(assumptions[1], wellFormedAnonymisationHeapsCondition),
                      validity);

        return addWdToValidityTerm(validity, updates, heaps, anonOutHeaps,
                                   localInVariables, localOutVariables, bc,
                                   configurator, services, tb);
    }

    private static Term addWdToValidityTerm(Term validity, final Term[] updates,
                                            final List<LocationVariable> heaps,
                                            Map<LocationVariable, Function> anonOutHeaps,
                                            final ImmutableSet<ProgramVariable> localInVariables,
                                            final ImmutableSet<ProgramVariable> localOutVariables,
                                            final BlockContract bc,
                                            final GoalsConfigurator configurator,
                                            final Services services,
                                            final TermBuilder tb) {
        if (WellDefinednessCheck.isOn()) {
            final Term wdUpdate = services.getTermBuilder().parallel(updates[1], updates[2]);

            Term localAnonUpdate =
                    createLocalAnonUpdate(localOutVariables, services, tb);

            if (localAnonUpdate == null) {
                localAnonUpdate = tb.skip();
            }

            Term wellDefinedness = configurator.setUpWdGoal(null,
                    bc, wdUpdate,
                    localAnonUpdate, heaps.get(0),
                    anonOutHeaps.get(heaps.get(0)),
                    localInVariables);

            validity = tb.and(wellDefinedness, validity);
        }
        return validity;
    }

    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("contract", contract.getName());
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof FunctionalBlockContractPO)) {
            return false;
        }

        FunctionalBlockContractPO other = (FunctionalBlockContractPO) po;
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
        if (!(obj instanceof FunctionalBlockContractPO)) {
            return false;
        }
        FunctionalBlockContractPO other = (FunctionalBlockContractPO) obj;
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
        final IProgramMethod pm = getProgramMethod();

        final StatementBlock block = getBlock();
        final ProgramVariable selfVar =
                tb.selfVar(pm, getCalleeKeYJavaType(), makeNamesUnique);
        register(selfVar, services);
        final Term selfTerm = selfVar == null ? null : tb.var(selfVar);

        final List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        final ImmutableSet<ProgramVariable> localInVariables =
                MiscTools.getLocalIns(block, services);
        final ImmutableSet<ProgramVariable> localOutVariables =
                MiscTools.getLocalOuts(block, services);

        Map<LocationVariable, Function> anonOutHeaps =
                createAnonOutHeaps(heaps, contract, services, tb);
        final BlockContract.Variables variables = new VariablesCreatorAndRegistrar(
                null, contract.getPlaceholderVariables(), services
                ).createAndRegister(selfTerm, false);
        final ProgramVariable exceptionParameter =
                KeYJavaASTFactory.localVariable(services.getVariableNamer()
                        .getTemporaryNameProposal("e"), variables.exception.getKeYJavaType());

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
                new ConditionsAndClausesBuilder(contract.getBlockContract(), heaps, variables,
                        selfTerm, services);

        final Term[] assumptions =
                createAssumptions(pm, selfVar, heaps, localInVariables,
                                  conditionsAndClausesBuilder, services);

        final Term[] postconditions = createPostconditions(conditionsAndClausesBuilder);

        Map<LocationVariable, Function> anonHeaps = createAnonHeaps(heaps, services, tb);

        final Term[] updates =
                createUpdates(variables, heaps, anonHeaps, services);

        final GoalsConfigurator configurator =
                setUpGoalConfigurator(block, selfVar, selfTerm, variables, services, tb);

        final Term validity = setUpValidityTerm(heaps, anonHeaps, anonOutHeaps,
                                                localInVariables, localOutVariables,
                                                exceptionParameter, assumptions,
                                                postconditions, updates,
                                                contract.getBlockContract(),
                                                conditionsAndClausesBuilder,
                                                configurator, services, tb);
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

    private GoalsConfigurator
                setUpGoalConfigurator(final StatementBlock block,
                                      final ProgramVariable selfVar,
                                      final Term selfTerm,
                                      final BlockContract.Variables variables,
                                      final Services services,
                                      final TermBuilder tb) {
        final KeYJavaType kjt = getCalleeKeYJavaType();
        final TypeRef typeRef =
                new TypeRef(new ProgramElementName(kjt.getName()), 0, selfVar, kjt);
        final ExecutionContext ec =
                new ExecutionContext(typeRef, getProgramMethod(), selfVar);
        final Instantiation inst =
                new Instantiation(tb.skip(), tb.tt(), contract.getModality(),
                                  selfTerm, block, ec);
        return new GoalsConfigurator(null, new TermLabelState(), inst,
                                     contract.getBlockContract().getLabels(),
                                     variables, null, services, null);
    }

    private Term[] createAssumptions(final IProgramMethod pm,
                                     final ProgramVariable selfVar,
                                     final List<LocationVariable> heaps,
                                     final ImmutableSet<ProgramVariable>
                                                localInVariables,
                                     final ConditionsAndClausesBuilder
                                                conditionsAndClausesBuilder,
                                     final Services services) {
        final Term precondition = conditionsAndClausesBuilder.buildPrecondition();
        final Term wellFormedHeapsCondition =
                conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final Term reachableInCondition =
                conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);
        return new Term[] {
            precondition, wellFormedHeapsCondition, reachableInCondition,
            generateSelfNotNull(pm, selfVar),
            generateSelfCreated(heaps, pm, selfVar, services),
            generateSelfExactType(pm, selfVar, getCalleeKeYJavaType())};
    }
}