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
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RemovePostTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.SplitPostTacletBuilder;
import de.uka.ilkd.key.speclang.InformationFlowContract;

import java.io.IOException;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Properties;


/**
 *
 * @author christoph
 */
public class InfFlowContractPO extends AbstractOperationPO
        implements ContractPO, InfFlowRelatedPO {

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
        addLabeledIFSymbol(finalTerm);

        // register final term, taclets and collect class axioms
        assignPOTerms(finalTerm);
        collectClassAxioms(contract.getKJT());

        for (final NoPosTacletApp t: taclets) {
            if (t.taclet().name().toString().startsWith("Class_invariant_axiom")) {
                // FIXME: Bla!
                addIFSymbol(t.taclet());
            }
        }

        // create and add split-post and remove-post taclets
        final SplitPostTacletBuilder splitPostTB = new SplitPostTacletBuilder();
        final ArrayList<Taclet> splitPostTaclets =
                splitPostTB.generateTaclets(post, services);
        for (final Taclet t : splitPostTaclets) {
            taclets = taclets.add(NoPosTacletApp
                    .createFixedNoPosTacletApp(t,
                                               SVInstantiations.EMPTY_SVINSTANTIATIONS,
                                               services));
            initConfig.getProofEnv().registerRule(t, AxiomJustification.INSTANCE);
            addIFSymbol(t);
            addIFSymbol(((RewriteTaclet)t).find());
        }
        final RemovePostTacletBuilder removePostTB = new RemovePostTacletBuilder();
        final ArrayList<Taclet> removePostTaclets =
                removePostTB.generateTaclets(post, services);
        for (final Taclet t : removePostTaclets) {
            taclets = taclets.add(NoPosTacletApp
                    .createFixedNoPosTacletApp(t,
                                               SVInstantiations.EMPTY_SVINSTANTIATIONS,
                                               services));
            initConfig.getProofEnv().registerRule(t, AxiomJustification.INSTANCE);
            addIFSymbol(t);
            addIFSymbol(((RewriteTaclet)t).find());
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
