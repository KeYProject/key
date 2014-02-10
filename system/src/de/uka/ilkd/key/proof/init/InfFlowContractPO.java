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
import de.uka.ilkd.key.proof.Proof;
import static de.uka.ilkd.key.proof.init.AbstractPO.TB;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.speclang.InformationFlowContract;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.Properties;


/**
 *
 * @author christoph
 */
public class InfFlowContractPO extends AbstractOperationPO
        implements ContractPO, InfFlowLeavePO {

    private final InformationFlowContract contract;

    private final ProofObligationVars symbExecVars;

    private final IFProofObligationVars ifVars;

    /**
     * For saving and loading Information-Flow proofs, we need to remember the
     * according taclets, program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();

    public InfFlowContractPO(InitConfig initConfig,
                             InformationFlowContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;

        // generate proof obligation variables
        final IProgramMethod pm = contract.getTarget();
        symbExecVars =
                new ProofObligationVars(pm, contract.getKJT(), services);

        assert (symbExecVars.pre.self == null) == (pm.isStatic());
        ifVars = new IFProofObligationVars(symbExecVars, services);

        // add new information flow symbols
        // (by the way: why only formal parameters?)
        for (Term formalParam : symbExecVars.formalParams) {
            addIFSymbol(formalParam);
        }
        for (Term formalParam : ifVars.c1.formalParams) {
            addIFSymbol(formalParam);
        }
        for (Term formalParam : ifVars.c2.formalParams) {
            addIFSymbol(formalParam);
        }
    }

    @Override
    public void readProblem() throws ProofInputException {

        // create proof obligation
        InfFlowPOSnippetFactory f =
                POSnippetFactory.getInfFlowFactory(contract, ifVars.c1,
                                                   ifVars.c2, services);
        final Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);
        final Term post =
                f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);
        final Term finalTerm = TB.imp(selfComposedExec, post);
        addLabeledIFSymbol(selfComposedExec);

        // register final term, taclets and collect class axioms
        assignPOTerms(finalTerm);
        collectClassAxioms(contract.getKJT());

        for (final NoPosTacletApp t: taclets) {
            if (t.taclet().name().toString().startsWith("Class_invariant_axiom")) {
                addIFSymbol(t.taclet());
            }
        }
    }


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof InfFlowContractPO)) {
            return false;
        }
        final InfFlowContractPO cPO = (InfFlowContractPO) po;
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
        return (InformationFlowContract) contract;
    }


    public IFProofObligationVars getIFVars() {
        return ifVars;
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
    public final void addIFSymbol(Term t) {
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
    public IFProofObligationVars getLeaveIFVars() {
        return getIFVars();
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
    protected ImmutableList<StatementBlock> buildOperationBlocks(
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
}
