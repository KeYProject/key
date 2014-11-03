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
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.InfFlowSpec;

public class LoopInvExecutionPO extends AbstractOperationPO
        implements InfFlowCompositePO {
    
    private final LoopInvariant loopInvariant;

    private final ProofObligationVars symbExecVars;

    private final Term guardTerm;

    private final Goal initiatingGoal;

    private final ExecutionContext context;

    /**
     * For saving and loading Information-Flow proofs, we need to remember the
     * according taclets, program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();

    /** To be used only for auxiliary proofs where the services object of
     * the actual proof has to be used instead of the initial services form
     * the InitConfig.
     */
    public LoopInvExecutionPO(InitConfig initConfig,
                              LoopInvariant loopInv,
                              ProofObligationVars symbExecVars,
                              Goal initiatingGoal,
                              ExecutionContext context,
                              Term guardTerm,
                              Services services) {
        this(initConfig, loopInv, symbExecVars, initiatingGoal, context,
             guardTerm);
        this.environmentServices = services;
    }


    public LoopInvExecutionPO(InitConfig initConfig,
                              LoopInvariant loopInv,
                              ProofObligationVars symbExecVars,
                              Goal initiatingGoal,
                              ExecutionContext context,
                              Term guardTerm) {
        super(initConfig,
              ContractFactory.generateContractName(loopInv.getName(),
                                                   loopInv.getKJT(),
                                                   loopInv.getTarget(),
                                                   loopInv.getTarget().getContainerType(),
                                                   loopInv.getLoop().getStartPosition().getLine()));
        this.loopInvariant = loopInv;
        this.symbExecVars = symbExecVars;
        this.initiatingGoal = initiatingGoal;
        this.context = context;
        this.guardTerm = guardTerm;

        // consistensy check
        assert preAndPostExpressionsEqual() :
                "Information flow loop invariant malformed. Pre expressions" +
                "do not match post expressions.";
    }


    private boolean preAndPostExpressionsEqual() {
        for (InfFlowSpec infFlowSpec: loopInvariant.getInfFlowSpecs(environmentServices)) {
            if(infFlowSpec.preExpressions == infFlowSpec.postExpressions) {
                return false;
            }
        }
        return true;
    }


    @Override
    public void readProblem() throws ProofInputException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory =
                POSnippetFactory.getBasicFactory(loopInvariant, symbExecVars,
                                                 context, guardTerm, environmentServices);

        // symbolic execution
        Term symExec =
                symbExecFactory.create(BasicPOSnippetFactory.Snippet.LOOP_EXEC_WITH_INV);

        // final symbolic execution term
        Term finalTerm = tb.applyElementary(symbExecVars.pre.heap,
                                            tb.not(symExec));

        // register final term
        assignPOTerms(finalTerm);

        // add class axioms
        Proof initiatingProof = initiatingGoal.proof();
        if (initiatingProof != null) {
            // proof is not loaded
            final AbstractOperationPO initiatingPO =
                    (AbstractOperationPO) specRepos.getProofOblInput(initiatingProof);
            taclets = initiatingPO.getInitialTaclets();
        }
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

    public Term getGuard() {
        return guardTerm;
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
        return loopInvariant.getName();
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
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars,
                                       Services services) {
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
                                    Map<Term, Term> heapToAtPre,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars,
                                    Services services) {
        throw new UnsupportedOperationException("Not supported any more. " +
                "Please use the POSnippetFactory instead.");
    }
}
