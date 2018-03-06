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
       }
       else {
           baseContractName = contractName.substring(0, ind);
       }
       final Contract contract =
               initConfig.getServices().getSpecificationRepository()
                                .getContractByName(baseContractName);
       if (contract == null) {
           throw new RuntimeException("Contract not found: " + baseContractName);
       }
       else {
           ProofOblInput po = contract.createProofObl(initConfig);
           return new LoadedPOContainer(po, proofNum);
       }
    }
    
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("contract", contract.getName());
    }

    public static Map<Boolean,String> TRANSACTION_TAGS = new LinkedHashMap<Boolean,String>();

    private TermBuilder tb;
    private FunctionalBlockContract contract;
    private InitConfig proofConfig;

    static {
      TRANSACTION_TAGS.put(false, "transaction_inactive");
      TRANSACTION_TAGS.put(true, "transaction_active");
    }

    public FunctionalBlockContractPO(InitConfig initConfig,
            FunctionalBlockContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
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
    public boolean equals(Object obj) {
    	if (!(obj instanceof FunctionalBlockContractPO)) {
    		return false;
    	}
    	
    	FunctionalBlockContractPO other = (FunctionalBlockContractPO) obj;
    	return contract.equals(other.contract)
    			&& environmentConfig.equals(other.environmentConfig);
    }

    @Override
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;
        final boolean makeNamesUnique = true;
        final Services services = postInit();
        final IProgramMethod pm = getProgramMethod();
        
        final StatementBlock block = getBlock();
        final ProgramVariable selfVar = tb.selfVar(pm, getCalleeKeYJavaType(), makeNamesUnique);
        register(selfVar, services);
        final Term selfTerm = selfVar == null ? null : tb.var(selfVar);

        final TermLabelState termLabelState = new TermLabelState();

        final List<LocationVariable> heaps = HeapContext.getModHeaps(services, false);
        final ImmutableSet<ProgramVariable> localInVariables =
                MiscTools.getLocalIns(block, services);
        final ImmutableSet<ProgramVariable> localOutVariables =
                MiscTools.getLocalOuts(block, services);
        
        Map<LocationVariable, Function> anonOutHeaps = new LinkedHashMap<LocationVariable, Function>(40);
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

        final BlockContract.Variables variables = new VariablesCreatorAndRegistrar(
                null, contract.getPlaceholderVariables(), services
                ).createAndRegister(selfTerm, false);
        
        final ProgramVariable exceptionParameter =
                KeYJavaASTFactory.localVariable(services.getVariableNamer()
                        .getTemporaryNameProposal("e"), variables.exception.getKeYJavaType());

        final ConditionsAndClausesBuilder conditionsAndClausesBuilder =
                new ConditionsAndClausesBuilder(contract.getBlockContract(), heaps, variables,
                                                selfTerm, services);
        final Term precondition = conditionsAndClausesBuilder.buildPrecondition();
        final Term wellFormedHeapsCondition =
                conditionsAndClausesBuilder.buildWellFormedHeapsCondition();
        final Term reachableInCondition =
                conditionsAndClausesBuilder.buildReachableInCondition(localInVariables);
        final Map<LocationVariable, Term> modifiesClauses =
                conditionsAndClausesBuilder.buildModifiesClauses();

        final Term postcondition = conditionsAndClausesBuilder.buildPostcondition();
        final Term frameCondition = conditionsAndClausesBuilder.buildFrameCondition(modifiesClauses);

        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term outerRemembranceUpdate = updatesBuilder.buildOuterRemembranceUpdate();
        
        Map<LocationVariable, Function> anonHeaps = new LinkedHashMap<LocationVariable, Function>(40);
        final TermBuilder tb = services.getTermBuilder();
        
        for (LocationVariable heap : heaps) {
            final String anonymisationName =
                    tb.newName(BlockContractBuilders.ANON_IN_PREFIX + heap.name());
            final Function anonymisationFunction =
                    new Function(new Name(anonymisationName), heap.sort(), true);
            services.getNamespaces().functions().addSafely(anonymisationFunction);
            anonHeaps.put(heap, anonymisationFunction);
        }
        
        final Term anonInUpdate = updatesBuilder.buildAnonInUpdate(anonHeaps);
        
        final KeYJavaType kjt = getCalleeKeYJavaType();
        
        final GoalsConfigurator configurator = new GoalsConfigurator(null,
                termLabelState,
                new Instantiation(
                        tb.skip(),
                        tb.tt(), 
                        contract.getModality(),
                        selfTerm,
                        block,
                        new ExecutionContext(
                                new TypeRef(new ProgramElementName(kjt.getName()), 0, selfVar, kjt),
                                getProgramMethod(),
                                selfVar)
                ),
                contract.getBlockContract().getLabels(),
                variables,
                null,
                services,
                null);
        
        Term validity = configurator.setUpValidityGoal(null,
                new Term[] { outerRemembranceUpdate, anonInUpdate, remembranceUpdate },
                new Term[] { precondition, wellFormedHeapsCondition, reachableInCondition },
                new Term[] { postcondition, frameCondition },
                exceptionParameter,
                conditionsAndClausesBuilder.getTerms());
        
        if (WellDefinednessCheck.isOn()) {
            final Term wdUpdate = services.getTermBuilder().parallel(anonInUpdate, remembranceUpdate);
            
            Term localAnonUpdate = null;
            for(ProgramVariable pv : localOutVariables) {
                final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
                final Function anonFunc = new Function(anonFuncName, pv.sort(), true);
                services.getNamespaces().functions().addSafely(anonFunc);
                final Term elemUpd = tb.elementary((LocationVariable)pv, tb.func(anonFunc))
                        ;
                if(localAnonUpdate == null) {
                    localAnonUpdate = elemUpd;
                } else {
                    localAnonUpdate = tb.parallel(localAnonUpdate, elemUpd);
                }
            }
            
            if (localAnonUpdate == null) {
                localAnonUpdate = tb.skip();
            }
            
            Term wellDefinedness = configurator.setUpWdGoal(null,
                    contract.getBlockContract(), wdUpdate,
                    localAnonUpdate, heaps.get(0),
                    anonOutHeaps.get(heaps.get(0)),
                    localInVariables);
            
            assignPOTerms(tb.and(wellDefinedness, validity));
        } else {
            assignPOTerms(validity);
        }
        
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

    @Override
    public Contract getContract() {
        return contract;
    }

    @Override
    public Term getMbyAtPre() {
        throw new UnsupportedOperationException();
    }
}
