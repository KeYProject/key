package de.uka.ilkd.key.speclang;

import java.util.List;
import java.util.Map;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IObserverFunction;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ContractPO;
import de.uka.ilkd.key.proof.init.FunctionalBlockContractPO;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProofOblInput;

/**
 * This class is only used to generate a proof obligation for a block
 * (see {@link FunctionalBlockContractPO}.
 * 
 * If a block is encountered during a proof, {@link BlockContract} is used instead.
 */
public class FunctionalBlockContract implements Contract {
    
    final BlockContract contract;
    final int id;
    
    public FunctionalBlockContract(BlockContract contract) {
        this(contract, Contract.INVALID_ID);
    }
    
    public FunctionalBlockContract(BlockContract contract, int id) {
        this.contract = contract;
        this.id = id;
    }

    @Override
    public String getName() {
        return "Block Contract Separate";
    }

    @Override
    public String getDisplayName() {
        return getName();
    }

    @Override
    public VisibilityModifier getVisibility() {
        assert false;
        return null;
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
    public IObserverFunction getTarget() {
        return contract.getTarget();
    }

    @Override
    public boolean hasMby() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public Term getMby() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getMby(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getMby(Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public OriginalVariables getOrigVars() {
        BlockContract.Variables vars = contract.getPlaceholderVariables();
        return new OriginalVariables(
                vars.self,
                vars.result,
                vars.exception,
                vars.remembranceLocalVariables,
                null
        );
    }

    @Override
    public Term getPre(LocationVariable heap, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getPre(List<LocationVariable> heapContext,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getPre(LocationVariable heap, Term heapTerm, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getPre(List<LocationVariable> heapContext,
            Map<LocationVariable, Term> heapTerms, Term selfTerm,
            ImmutableList<Term> paramTerms, Map<LocationVariable, Term> atPres,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getDep(LocationVariable heap, boolean atPre,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, ? extends ProgramVariable> atPreVars,
            Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getDep(LocationVariable heap, boolean atPre, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms,
            Map<LocationVariable, Term> atPres, Services services) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getRequires(LocationVariable heap) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getAssignable(LocationVariable heap) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getAccessible(ProgramVariable heap) {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getGlobalDefs() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Term getGlobalDefs(LocationVariable heap, Term heapTerm,
            Term selfTerm, ImmutableList<Term> paramTerms, Services services) {
        // TODO Auto-generated method stub
        return null;
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
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public boolean transactionApplicableContract() {
        // TODO Auto-generated method stub
        return false;
    }

    @Override
    public String proofToString(Services services) {
        return contract.toString();
    }

    @Override
    public ContractPO createProofObl(InitConfig initConfig) {
       return new FunctionalBlockContractPO(initConfig, this);
    }

    @Override
    public ProofOblInput getProofObl(Services services) {
        // TODO Auto-generated method stub
        return null;
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
        return new FunctionalBlockContract(contract, newId);
    }

    @Override
    public Contract setTarget(KeYJavaType newKJT, IObserverFunction newPM) {
        return new FunctionalBlockContract(contract.setTarget(newKJT, newPM), id);
    }

    @Override
    public String getTypeName() {
        return ContractFactory.generateContractTypeName("BlockContract", getKJT(), getTarget(), getKJT());
    }

    @Override
    public boolean hasSelfVar() {
        return contract.getVariables().self != null;
    }

    public boolean hasModifiesClause(LocationVariable heap) {
        return contract.hasModifiesClause(heap);
    }

    public BlockContract getBlockContract() {
        return contract;
    }

    public StatementBlock getBlock() {
        return contract.getBlock();
    }

    public IProgramMethod getMethod() {
        return contract.getMethod();
    }

}
