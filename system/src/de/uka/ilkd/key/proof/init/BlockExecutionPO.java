/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.ContractFactory;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.InformationFlowContractImpl;
import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Properties;


/**
 *
 * @author christoph
 */
public class BlockExecutionPO extends AbstractOperationPO
        implements ContractPO, InfFlowRelatedPO {

    private final BlockContract contract;
    private final InformationFlowContract generatedIFContract;
    private final ProofObligationVars symbExecVars;
    private final Goal initiatingGoal;
    private final ExecutionContext context;

    /**
     * For saving and loading Information-Flow proofs, we need to remember the
     * according taclets, program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();

    public BlockExecutionPO(InitConfig initConfig,
                            BlockContract contract,
                            ProofObligationVars symbExecVars,
                            Goal initiatingGoal,
                            ExecutionContext context) {
        super(initConfig,
              ContractFactory.generateContractName(contract.getName(), contract.getKJT(),
                                                   contract.getTarget(),
                                                   contract.getTarget().getContainerType(),
                                                   contract.getBlock().getStartPosition().getLine()));
        this.contract = contract;
        this.generatedIFContract =
                new InformationFlowContractImpl(contract, services);
        this.symbExecVars = symbExecVars;
        this.initiatingGoal = initiatingGoal;
        this.context = context;
    }

    @Override
    public void readProblem() throws ProofInputException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory =
                POSnippetFactory.getBasicFactory(contract, symbExecVars,
                                                 context, services);

        // precondition
        final Term freePre =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final Term contractPre =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        final Term pre = TB.and(freePre, contractPre);

        // symbolic execution
        final Term symExec =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.BLOCK_EXEC);
        addIFSymbol(pre);
        addIFSymbol(symExec);

        // final symbolic execution term
        final Term finalTerm = TB.applyElementary(services, symbExecVars.pre.heap,
                                                  TB.not(TB.and(pre, symExec)));

        // register final term
        assignPOTerms(finalTerm);

        // add class axioms
        final Proof initiatingProof = initiatingGoal.proof();
        final AbstractOperationPO initiatingPO =
                specRepos.getPOForProof(initiatingProof) != null ? // if proof is loaded
                (AbstractOperationPO) specRepos.getPOForProof(initiatingProof)
                : new SymbolicExecutionPO(initConfig, generatedIFContract,
                                          symbExecVars, initiatingGoal);
        taclets = initiatingPO.getInitialTaclets();
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof BlockExecutionPO)) {
            return false;
        }
        final BlockExecutionPO cPO = (BlockExecutionPO) po;
        return contract.equals(cPO.contract);
    }


    @Override
    public Term getMbyAtPre() {
        if (contract.hasMby()) {
            return symbExecVars.pre.mbyAtPre;
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
        return generatedIFContract;
    }


    public Goal getInitiatingGoal() {
        return initiatingGoal;
    }


    public ExecutionContext getExecutionContext() {
        return context;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("Non-interference contract", contract.getUniqueName());
    }

    public InfFlowProofSymbols getIFSymbols() {
        assert infFlowSymbols != null;
        return infFlowSymbols;
    }

    public void addIFSymbol(Term t) {
        assert t != null;
        infFlowSymbols.add(t);
    }

    public void addIFSymbol(Named n) {
        assert n != null;
        infFlowSymbols.add(n);
    }

    public void addLabeledIFSymbol(Term t) {
        assert t != null;
        infFlowSymbols.addLabeled(t);
    }

    public void addLabeledIFSymbol(Named n) {
        assert n != null;
        infFlowSymbols.addLabeled(n);
    }

    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols) {
        assert symbols != null;
        infFlowSymbols = infFlowSymbols.unionLabeled(symbols);
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
