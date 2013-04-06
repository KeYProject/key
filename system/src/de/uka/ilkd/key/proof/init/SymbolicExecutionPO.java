/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.ContractFactory;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Properties;


/**
 *
 * @author christoph
 */
public class SymbolicExecutionPO extends AbstractOperationPO
        implements ContractPO, InfFlowRelatedPO {

    private final InformationFlowContract contract;
    private final ProofObligationVars symbExecVars;
    private final Goal initiatingGoal;


    public SymbolicExecutionPO(InitConfig initConfig,
                               InformationFlowContract contract,
                               ProofObligationVars symbExecVars,
                               Goal initiatingGoal) {
        super(initConfig,
              ContractFactory.generateContractName(contract.getPODisplayName(),
                                                   contract.getKJT(),
                                                   contract.getTarget(),
                                                   contract.getTarget().getContainerType(),
                                                   contract.getTarget().getStartPosition().getLine()));
        this.contract = contract;
        this.symbExecVars = symbExecVars;
        this.initiatingGoal = initiatingGoal;
    }


    @Override
    public void readProblem() throws ProofInputException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory =
                POSnippetFactory.getBasicFactory(contract, symbExecVars, services);

        // precondition
        final Term freePre =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final Term contractPre =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        final Term pre = TB.and(freePre, contractPre);

        // symbolic execution
        Term symExec =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.SYMBOLIC_EXEC);

        // final symbolic execution term
        Term finalTerm = TB.not(TB.and(pre, symExec));

        // register final term
        assignPOTerms(finalTerm);

        // add class axioms
        Proof initiatingProof = initiatingGoal.proof();
        AbstractOperationPO initatingPO =
                (AbstractOperationPO) services.getSpecificationRepository()
                                                    .getPOForProof(initiatingProof);
        taclets = initatingPO.getInitialTaclets();
    }


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof SymbolicExecutionPO)) {
            return false;
        }
        SymbolicExecutionPO cPO = (SymbolicExecutionPO) po;
        return contract.equals(cPO.contract);
    }


    @Override
    public Term getMbyAtPre() {
        if (contract.hasMby()) {
            return symbExecVars.mbyAtPre;
        } else {
            return null;
        }
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected String buildPOName(boolean transactionFlag) {
        return getContract().getName();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected IProgramMethod getProgramMethod() {
        return contract.getTarget();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected boolean isTransactionApplicable() {
        return false;
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
    }


    /**
     * {@inheritDoc}
     */
    @Override
    protected Modality getTerminationMarker() {
        return getContract().getModality();
    }


    @Override
    public InformationFlowContract getContract() {
        return contract;
    }


    public Goal getInitiatingGoal() {
        return initiatingGoal;
    }



    /**
     * {@inheritDoc}
     */
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("contract", contract.getName());
    }


    /**
     * Instantiates a new proof obligation with the given settings.
     * <p/>
     * @param initConfig The already load {@link InitConfig}.
     * @param properties The settings of the proof obligation to instantiate.
     * @return The instantiated proof obligation.
     * @throws IOException Occurred Exception.
     */
    public static LoadedPOContainer loadFrom(InitConfig initConfig,
                                             Properties properties) throws IOException {
        String contractName = properties.getProperty("contract");
        SpecificationRepository specs =
                initConfig.getServices().getSpecificationRepository();
        final Contract contract = specs.getContractByName(contractName);
        if (contract == null) {
            throw new RuntimeException("Contract not found: " + contractName);
        } else {
            ProofOblInput po = contract.createProofObl(initConfig);
            return new LoadedPOContainer(po, 0);
        }
    }

    
    // the following code is legacy code
    @Override
    @Deprecated
    protected StatementBlock buildOperationBlock(
            ImmutableList<LocationVariable> formalParVars,
                                                 ProgramVariable selfVar,
                                                 ProgramVariable resultVar) {
        throw new UnsupportedOperationException("Not supported any more. " +
                 "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected Term getPre(List<LocationVariable> modHeaps,
                          ProgramVariable selfVar,
                          ImmutableList<ProgramVariable> paramVars,
                          Map<LocationVariable, LocationVariable> atPreVars,
                          Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                 "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected Term getPost(List<LocationVariable> modHeaps,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           ProgramVariable resultVar,
                           ProgramVariable exceptionVar,
                           Map<LocationVariable, LocationVariable> atPreVars,
                           Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                 "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected Term buildFrameClause(List<LocationVariable> modHeaps,
                                    Map<LocationVariable, Map<Term, Term>> heapToAtPre,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars) {
        throw new UnsupportedOperationException("Not supported any more. " +
                 "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars) {
        throw new UnsupportedOperationException("Not supported any more. " +
                 "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected Term generateMbyAtPreDef(Term selfVar,
                                       ImmutableList<Term> paramVars) {
        throw new UnsupportedOperationException("Not supported any more. " +
                 "Please use the POSnippetFactory instead.");
    }
}
