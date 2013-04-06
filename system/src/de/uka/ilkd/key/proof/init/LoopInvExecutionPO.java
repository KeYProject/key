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
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
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
        Term finalTerm = TB.applyElementary(services, symbExecVars.heap,
                                            TB.not(TB.and(inv, symExec)));

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
        properties.setProperty("loop_invariant", loopInvariant.getName());
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
        String loopInvName = properties.getProperty("loop_invariant");
        SpecificationRepository specs =
                initConfig.getServices().getSpecificationRepository();
        final LoopInvariant loopInv = specs.getLoopInvariantByName(loopInvName);
        if (loopInv == null) {
            throw new RuntimeException("Loop Invariant not found: " + loopInvName);
        } else {
            ProofOblInput po = new InfFlowContractPO(initConfig, null);
            return new LoadedPOContainer(po, 0);
        }
    }

    @Override
    public InformationFlowContract getContract() {
        return generatedIFContract;
    }

    @Override
    @Deprecated
    public Term getMbyAtPre() {
        throw new UnsupportedOperationException("Not a contract.");
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

}
