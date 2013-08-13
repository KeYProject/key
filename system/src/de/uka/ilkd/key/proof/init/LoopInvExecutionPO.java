package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Properties;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.speclang.ContractFactory;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.speclang.InformationFlowContractImpl;
import de.uka.ilkd.key.speclang.LoopInvariant;

public class LoopInvExecutionPO extends AbstractOperationPO
        implements ContractPO, InfFlowRelatedPO {
    
    private final LoopInvariant loopInvariant;

    private final InformationFlowContract generatedIFContract;

    private final ProofObligationVars symbExecVars;

    private final Goal initiatingGoal;

    private final ExecutionContext context;

    /**
     * For saving and loading Information-Flow proofs, we need to remember the
     * according taclets, program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();

    public LoopInvExecutionPO(InitConfig initConfig,
                              LoopInvariant loopInv,
                              ProofObligationVars symbExecVars,
                              Goal initiatingGoal,
                              ExecutionContext context) {
        super(initConfig,
              ContractFactory.generateContractName(loopInv.getName(),
                                                   loopInv.getKJT(),
                                                   loopInv.getTarget(),
                                                   loopInv.getTarget().getContainerType(),
                                                   loopInv.getLoop().getStartPosition().getLine()));
        this.generatedIFContract =
                new InformationFlowContractImpl(loopInv, services);
        this.loopInvariant = loopInv;
        this.symbExecVars = symbExecVars;
        this.initiatingGoal = initiatingGoal;
        this.context = context;
    }


    @Override
    public void readProblem() throws ProofInputException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory =
                POSnippetFactory.getBasicFactory(loopInvariant, symbExecVars,
                                                 context, services);

        // loop invariant
        final Term freeInv =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_INV);
        final Term loopInv =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_INV);
        final Term inv = TB.and(freeInv, loopInv);

        // symbolic execution
        Term symExec =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_EXEC);

        // final symbolic execution term
        Term finalTerm = TB.applyElementary(services, symbExecVars.pre.heap,
                                            TB.not(TB.and(inv, symExec)));

        // register final term
        assignPOTerms(finalTerm);

        // add class axioms
        Proof initiatingProof = initiatingGoal.proof();
        final AbstractOperationPO initiatingPO =
                specRepos.getPOForProof(initiatingProof) != null ? // if proof is loaded
                (AbstractOperationPO) specRepos.getPOForProof(initiatingProof)
                : new SymbolicExecutionPO(initConfig, generatedIFContract,
                                          symbExecVars, initiatingGoal);
        taclets = initiatingPO.getInitialTaclets();
    }

    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof LoopInvExecutionPO)) {
            return false;
        }
        LoopInvExecutionPO lPO = (LoopInvExecutionPO) po;
        return loopInvariant.equals(lPO.loopInvariant);
    }
    
    public LoopInvariant getLoopInvariant() {        
        return loopInvariant;
    }

    public Goal getInitiatingGoal() {
        return initiatingGoal;
    }

    public ExecutionContext getExecutionContext() {
        return context;
    }

    @Override
    protected IProgramMethod getProgramMethod() {
        return loopInvariant.getTarget();
    }

    @Override
    protected boolean isTransactionApplicable() {
        return false;
    }

    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        assert false;
        return loopInvariant.getKJT();
    }

    @Override
    protected Modality getTerminationMarker() {
        return Modality.BOX;
    }

    @Override
    protected String buildPOName(boolean transactionFlag) {
        return getContract().getName();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void fillSaveProperties(Properties properties) throws IOException {
        super.fillSaveProperties(properties);
        properties.setProperty("Non-interference contract", loopInvariant.getUniqueName());
    }


    @Override
    public InformationFlowContract getContract() {
        return generatedIFContract;
    }

    @Override
    public Term getMbyAtPre() {
                if (generatedIFContract.hasMby()) {
            return symbExecVars.pre.mbyAtPre;
        } else {
            return null;
        }
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
    @Deprecated
    protected StatementBlock buildOperationBlock(
            ImmutableList<LocationVariable> formalParVars,
            ProgramVariable selfVar, ProgramVariable resultVar) {
        throw new UnsupportedOperationException("Not supported any more. " +
                "Please use the POSnippetFactory instead.");
    }

    @Override
    @Deprecated
    protected ImmutableList<StatementBlock> buildOperationBlocks(
                                                                 ImmutableList<LocationVariable> formalParVars,
                                                                 ProgramVariable selfVar,
                                                                 ProgramVariable resultVar) {
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
    protected Term getPre(List<LocationVariable> modHeaps,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                "Please use the POSnippetFactory instead.");
    }

    @Override
    @Deprecated
    protected Term getPost(List<LocationVariable> modHeaps,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars,
            ProgramVariable resultVar, ProgramVariable exceptionVar,
            Map<LocationVariable, LocationVariable> atPreVars, Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                "Please use the POSnippetFactory instead.");
    }

    @Override
    @Deprecated
    protected Term buildFrameClause(List<LocationVariable> modHeaps,
            Map<LocationVariable, Map<Term, Term>> heapToAtPre,
            ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars) {
        throw new UnsupportedOperationException("Not supported any more. " +
                "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected Term getGlobalDefs(LocationVariable heap,
                                 Term heapTerm,
                                 Term selfTerm,
                                 ImmutableList<Term> paramTerms,
                                 Services services) {
        throw new UnsupportedOperationException("Not supported yet."); //To change body of generated methods, choose Tools | Templates.
    }

}
