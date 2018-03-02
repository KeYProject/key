package de.uka.ilkd.key.speclang;

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.function.UnaryOperator;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.init.FunctionalLoopContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;

public class FunctionalLoopContract implements Contract {
    
    private final LoopContract contract;
    private final int id;
    private final String name;
    private final String displayName;
    private final String typeName;
    
    FunctionalLoopContract(LoopContract contract) {
        this(contract, Contract.INVALID_ID);
    }
    
    FunctionalLoopContract(LoopContract contract, int id) {
        this.contract = contract;
        this.id = id;
        
        if (id != Contract.INVALID_ID) {
            contract.setFunctionalLoopContract(this);
        }
        
        name = generateName(contract.getBaseName(), str
                -> ContractFactory.generateContractName(str, getKJT(), getTarget(), getKJT(), id));
        displayName = generateName(contract.getBaseName(), str
                -> ContractFactory.generateDisplayName(str, getKJT(), getTarget(), getKJT(), id));
        typeName = generateName(contract.getBaseName(), str
                -> ContractFactory.generateContractTypeName(str, getKJT(), getTarget(), getKJT()));
    }
    
    private String generateName(String baseName, UnaryOperator<String> generator) {
        return Arrays.stream(baseName.split(SpecificationRepository.CONTRACT_COMBINATION_MARKER))
                .map(generator)
                .reduce((acc, curr)
                        -> acc + SpecificationRepository.CONTRACT_COMBINATION_MARKER + curr)
                .get();
    }

    @Override
    public String getName() {
        return name;
    }

    @Override
    public String getDisplayName() {
        return displayName;
    }

    @Override
    public VisibilityModifier getVisibility() {
        throw new UnsupportedOperationException();
    }

    @Override
    public KeYJavaType getKJT() {
        return contract.getKJT();
    }

    @Override
    public int id() {
        return id;
    }

    @Override
    public IProgramMethod getTarget() {
        return contract.getTarget();
    }

    @Override
    public boolean hasMby() {
        return contract.hasMby();
    }

    @Override
    public Term getMby() {
        return contract.getMby();
    }

    @Override
    public Term getMby(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services) {
        return contract.getMby(selfVar, services);
    }

    @Override
    public Term getMby(Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        return contract.getMby(heapTerms, selfTerm, atPres, services);
    }

    @Override
    public OriginalVariables getOrigVars() {
        return contract.getOrigVars();
    }

    @Override
    public Term getPre(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        @SuppressWarnings("unchecked")
        Map<LocationVariable, ProgramVariable> atPreVars0 =
            (Map<LocationVariable, ProgramVariable>) atPreVars;
        return contract.getPrecondition(
                heap,
                selfVar,
                atPreVars0.entrySet().stream().collect(Collectors
                        .<Map.Entry<LocationVariable, ProgramVariable>,
                            LocationVariable, LocationVariable>toMap(
                                    Map.Entry::getKey,
                                    entry -> (LocationVariable) entry.getValue()
                    )),
                services);
    }

    @Override
    public Term getPre(List<LocationVariable> heapContext,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        TermBuilder tb = services.getTermBuilder();
        Term result = null;
        
        for (LocationVariable heap : heapContext) {
            final Term p = getPre(heap, selfVar, paramVars, atPreVars, services);
            
            if (result == null) {
                result = p;
            } else {
                result = tb.and(result, p);
            }
        }
        
        return result;
    }

    @Override
    public Term getPre(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        return contract.getPrecondition(heap, heapTerm, selfTerm, atPres, services);
    }

    @Override
    public Term getPre(List<LocationVariable> heapContext,
            Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        TermBuilder tb = services.getTermBuilder();
        Term result = null;
        
        for (LocationVariable heap : heapContext) {
            final Term p = getPre(heap, heapTerms.get(heap), selfTerm, paramTerms, atPres, services);

            if (result == null) {
                result = p;
            } else if (p != null) {
                result = tb.and(result, p);
            }
        }
        
        return result;
    }

    @Override
    public Term getDep(LocationVariable heap, boolean atPre,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        return services.getTermBuilder().allLocs();
    }

    @Override
    public Term getDep(LocationVariable heap, boolean atPre, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms,
            Map<LocationVariable, Term> atPres, Services services) {
        return services.getTermBuilder().allLocs();
    }

    @Override
    public Term getRequires(LocationVariable heap) {
        return contract.getRequires(heap);
    }

    @Override
    public Term getAssignable(LocationVariable heap) {
        return contract.getAssignable(heap);
    }

    @Override
    public Term getAccessible(ProgramVariable heap) {
        throw new UnsupportedOperationException();
    }

    @Override
    public Term getGlobalDefs() {
        throw new UnsupportedOperationException();
    }

    @Override
    public Term getGlobalDefs(LocationVariable heap, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms, Services services) {
        throw new UnsupportedOperationException();
    }

    @Override
    public String getHTMLText(Services services) {
        return contract.getHtmlText(services);
    }

    @Override
    public String getPlainText(Services services) {
        return contract.getPlainText(services);
    }

    @Override
    public boolean toBeSaved() {
        return false;
    }

    @Override
    public boolean transactionApplicableContract() {
        return contract.isTransactionApplicable();
    }

    @Override
    public String proofToString(Services services) {
        return contract.toString();
    }

    @Override
    public ContractPO createProofObl(InitConfig initConfig) {
       return new FunctionalLoopContractPO(initConfig, this);
    }

    @Override
    public ProofOblInput getProofObl(Services services) {
        return services.getSpecificationRepository().getPO(this);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
            Contract contract) {
        assert contract instanceof FunctionalBlockContract;
        return new FunctionalBlockContractPO(initConfig, (FunctionalBlockContract) contract);
    }

    @Override
    public ProofOblInput createProofObl(InitConfig initConfig,
            Contract contract, boolean supportSymbolicExecutionAPI) {
        return createProofObl(initConfig, contract);
    }

    @Override
    public Contract setID(int newId) {
        return new FunctionalLoopContract(contract, newId);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new FunctionalLoopContract(contract.setTarget(newKJT, newPM), id);
    }

    @Override
    public String getTypeName() {
        return typeName;
    }

    @Override
    public boolean hasSelfVar() {
        return contract.getVariables().self != null;
    }

    public boolean hasModifiesClause(LocationVariable heap) {
        return contract.hasModifiesClause(heap);
    }

    public LoopContract getLoopContract() {
        return contract;
    }

    public StatementBlock getBlock() {
        return contract.getBlock();
    }

    public IProgramMethod getMethod() {
        return contract.getMethod();
    }

    public BlockSpecificationElement.Variables getPlaceholderVariables() {
        return contract.getPlaceholderVariables();
    }

    public Modality getModality() {
        return contract.getModality();
    }
}
