package de.uka.ilkd.key.proof.init;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.KeYJavaASTFactory;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.label.TermLabelState;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.BlockContractBuilders;
import de.uka.ilkd.key.rule.AbstractBlockContractRule.Instantiation;
import de.uka.ilkd.key.rule.BlockContractBuilders.ConditionsAndClausesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.UpdatesBuilder;
import de.uka.ilkd.key.rule.BlockContractBuilders.VariablesCreatorAndRegistrar;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.FunctionalBlockContract;
import de.uka.ilkd.key.speclang.HeapContext;
import de.uka.ilkd.key.util.MiscTools;

public class FunctionalBlockContractPO extends AbstractPO implements ContractPO {

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
    public void readProblem() throws ProofInputException {
        assert proofConfig == null;
        final boolean makeNamesUnique = true;
        final Services services = postInit();
        final IProgramMethod pm = getProgramMethod();
        final List<Term> termPOs = new ArrayList<Term>();
        
        final StatementBlock block = getBlock();
        final ProgramVariable selfVar = tb.selfVar(pm, getCalleeKeYJavaType(), makeNamesUnique);
        final Term selfTerm = tb.var(selfVar);
        register(selfVar, services);

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
                        tb.newName(BlockContractBuilders.ANONYMISATION_PREFIX + heap.name());
                final Function anonymisationFunction =
                        new Function(new Name(anonymisationName), heap.sort(), true);
                services.getNamespaces().functions().addSafely(anonymisationFunction);
                anonOutHeaps.put(heap, anonymisationFunction);
            }
        }

        final BlockContract.Variables variables = new VariablesCreatorAndRegistrar(
                null, contract.getPlaceholderVariables(), services
                ).createAndRegister(selfTerm);
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
        final Term wellFormedAnonymisationHeapsCondition =
                conditionsAndClausesBuilder
                .buildWellFormedAnonymisationHeapsCondition(anonOutHeaps);
        final Term reachableOutCondition =
                conditionsAndClausesBuilder.buildReachableOutCondition(localOutVariables);
        final Term atMostOneFlagSetCondition =
                conditionsAndClausesBuilder.buildAtMostOneFlagSetCondition();

        final UpdatesBuilder updatesBuilder = new UpdatesBuilder(variables, services);
        final Term remembranceUpdate = updatesBuilder.buildRemembranceUpdate(heaps);
        final Term wdUpdate = services.getTermBuilder().parallel(/*anonInUpdate*/tb.skip(), remembranceUpdate);
        
        Term anonOutUpdate = null;
        
        for (ProgramVariable pv : localOutVariables) {
            final Name anonFuncName = new Name(tb.newName(pv.name().toString()));
            final Function anonFunc = new Function(anonFuncName, pv.sort(), true);
            services.getNamespaces().functions().addSafely(anonFunc);
            final Term elemUpd = tb.elementary((LocationVariable)pv, tb.func(anonFunc));
            
            if (anonOutUpdate == null) {
                anonOutUpdate = elemUpd;
            } else {
                anonOutUpdate = tb.parallel(anonOutUpdate, elemUpd);
            }
        }
        
        if (anonOutUpdate == null) {
            anonOutUpdate = tb.skip();
        }
        
        final Term anonymisationUpdate =
                updatesBuilder.buildAnonymisationUpdate(anonOutHeaps,
                                                        modifiesClauses);
        
        termPOs.add(tb.imp(precondition, postcondition));
        
        assignPOTerms(termPOs.toArray(new Term[termPOs.size()]));
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
        return environmentConfig.deepCopy();
    }

    @Override
    public Contract getContract() {
        return contract;
    }

    @Override
    public Term getMbyAtPre() {
        // TODO Auto-generated method stub
        return null;
    }
}
