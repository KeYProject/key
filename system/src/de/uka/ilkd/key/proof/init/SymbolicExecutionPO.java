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
        implements ContractPO, InfFlowCompositePO {

    private final InformationFlowContract contract;
    private final ProofObligationVars symbExecVars;
    private final Goal initiatingGoal;

    /**
     * For saving and loading Information-Flow proofs, we need to remember the
     * according taclets, program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();

    /** To be used only for auxiliary proofs where the services object of
     * the actual proof has to be used instead of the initial services form
     * the InitConfig.
     */
    public SymbolicExecutionPO(InitConfig initConfig,
                               InformationFlowContract contract,
                               ProofObligationVars symbExecVars,
                               Goal initiatingGoal,
                               Services services) {
        this(initConfig, contract, symbExecVars, initiatingGoal);
        this.environmentServices = services;
    }


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
                POSnippetFactory.getBasicFactory(contract, symbExecVars,
                                                 initiatingGoal.proof().getServices());

        // symbolic execution under precondition
        final Term symExec =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.SYMBOLIC_EXEC_WITH_PRE);

        // register final term
        assignPOTerms(tb.not(symExec));

        // add class axioms
        final Proof initiatingProof = initiatingGoal.proof();
        if (initiatingProof != null) {
            // proof is not loaded
            final AbstractOperationPO initiatingPO =
                    (AbstractOperationPO) specRepos.getProofOblInput(initiatingProof);
            taclets = initiatingPO.getInitialTaclets();
        }
    }


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof SymbolicExecutionPO)) {
            return false;
        }
        final SymbolicExecutionPO cPO = (SymbolicExecutionPO) po;
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
        properties.setProperty("Non-interference contract", contract.getName());
    }

    @Override
    public InfFlowProofSymbols getIFSymbols() {
        assert infFlowSymbols != null;
        return infFlowSymbols;
    }

    @Override
    public void addIFSymbol(Term t) {
        assert t != null;
        infFlowSymbols.add(t);
    }

    @Override
    public void addIFSymbol(Named n) {
        assert n != null;
        infFlowSymbols.add(n);
    }

    @Override
    public void addLabeledIFSymbol(Term t) {
        assert t != null;
        infFlowSymbols.addLabeled(t);
    }

    @Override
    public void addLabeledIFSymbol(Named n) {
        assert n != null;
        infFlowSymbols.addLabeled(n);
    }

    @Override
    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols) {
        assert symbols != null;
        infFlowSymbols = infFlowSymbols.unionLabeled(symbols);
    }

    @Override
    protected Term getGlobalDefs(LocationVariable heap,
                                 Term heapTerm,
                                 Term selfTerm,
                                 ImmutableList<Term> paramTerms,
                                 Services services) {
        // information flow contracts do not have global defs
        return null;
    }



    @Override
    public InfFlowPO getChildPO() {
        Proof initiatingProof = getInitiatingGoal().proof();
        Services initiatingServices = initiatingProof.getServices();
        ProofOblInput initiatingPO =
                initiatingServices.getSpecificationRepository().getProofOblInput(initiatingProof);
        assert initiatingPO instanceof InfFlowPO : "Information flow auxiliary " +
                "proof started from within non-information flow proof!?!";
        return (InfFlowPO)initiatingPO;
    }


    @Override
    public IFProofObligationVars getLeaveIFVars() {
        return getChildPO().getLeaveIFVars();
    }


// the following code is legacy code
    @Override
    @Deprecated
    protected ImmutableList<StatementBlock> buildOperationBlocks(
            ImmutableList<LocationVariable> formalParVars,
            ProgramVariable selfVar,
            ProgramVariable resultVar,
            Services services) {
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
            Map<Term, Term> heapToAtPre, ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
            ImmutableList<ProgramVariable> paramVars, Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                "Please use the POSnippetFactory instead.");
    }
}