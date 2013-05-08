/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSnippetFactory;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RemovePostTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.SplitPostTacletBuilder;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import de.uka.ilkd.key.util.MiscTools;

import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
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

    private static InfFlowProofSymbols ifSymbols;


    public InfFlowContractPO(InitConfig initConfig,
                             InformationFlowContract contract) {
        super(initConfig, contract.getName());
        ifSymbols = new InfFlowProofSymbols();
        this.contract = contract;

        // generate proof obligation variables
        final IProgramMethod pm = contract.getTarget();
        symbExecVars =
                new ProofObligationVars(pm, contract.getKJT(), services,
                                        false, contract == null);
        assert (symbExecVars.self == null) == (pm.isStatic());
        ifVars = new IFProofObligationVars(symbExecVars, services, contract == null);
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

        // register final term, taclets and collect class axioms
        assignPOTerms(finalTerm);
        collectClassAxioms(contract.getKJT());

        for (final NoPosTacletApp t: taclets) {
            if (t.taclet().name().toString().startsWith("Class_invariant_axiom")) {
                addSymbol(t.taclet(), services);
            }
        }

        // create and add split-post and remove-post taclets
        final SplitPostTacletBuilder splitPostTB = new SplitPostTacletBuilder();
        final ArrayList<Taclet> splitPostTaclets = splitPostTB.generateTaclets(post);
        for (final Taclet t : splitPostTaclets) {
            taclets = taclets.add(NoPosTacletApp
                    .createFixedNoPosTacletApp(t,
                                               SVInstantiations.EMPTY_SVINSTANTIATIONS,
                                               services));
            initConfig.getProofEnv().registerRule(t, AxiomJustification.INSTANCE);
        }
        final RemovePostTacletBuilder tb = new RemovePostTacletBuilder();
        final ArrayList<Taclet> removePostTaclets = tb.generateTaclets(post);
        for (final Taclet t : removePostTaclets) {
            taclets = taclets.add(NoPosTacletApp
                    .createFixedNoPosTacletApp(t,
                                               SVInstantiations.EMPTY_SVINSTANTIATIONS,
                                               services));
            initConfig.getProofEnv().registerRule(t, AxiomJustification.INSTANCE);
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

    public static Taclet getTaclet(String name) {
        return symbols().getTaclet(name);
    }

    public static ProgramVariable getProgramVariable(String prefix) {
        return symbols().getProgramVariable(prefix);
    }

    public static FindTaclet loadFindTaclet(IProgramMethod pm, Services services) {
        Taclet res = null;
        if (!InfFlowContractPO.hasSymbols()) {
            InfFlowContractPO.newSymbols(
                    services.getProof().env().getInitConfig().activatedTaclets());
        }
        for (int j = 0; j < 10000; j++) {
            String name =
                    MiscTools.toValidTacletName("unfold computed formula " + j + " of " +
                                                pm.getFullName()).toString();
            res = InfFlowContractPO.getTaclet(name);
            if (res != null)
                return (FindTaclet)res;
        }
        assert false; // This should not happen
        return null;
    }

    public static Term loadFindTerm(IProgramMethod pm, Services services) {
        return loadFindTaclet(pm, services).find();
    }

    public static void newSymbols(ImmutableSet<Taclet> taclets) {
        InfFlowProofSymbols symbols = new InfFlowProofSymbols(taclets);
        ifSymbols = symbols;
    }

    private static InfFlowProofSymbols symbols() {
        assert ifSymbols != null;
        return ifSymbols;
    }

    public static boolean hasSymbols() {
        return ifSymbols != null;
    }

    public static void addSymbol(Object o) {
        assert o != null;
        symbols().add(o);
    }

    public static void addSymbols(ImmutableList<?> l) {
        assert l != null;
        assert !l.isEmpty();
        symbols().add(l);
    }

    public static void addSymbol(Object o, Services services) {
        if (!hasSymbols()) {
            ifSymbols =
                    new InfFlowProofSymbols(services.getProof()
                            .env().getInitConfig().activatedTaclets());
        }
        addSymbol(o);
    }

    public static void addSymbols(ImmutableList<?> l, Services services) {
        if (!hasSymbols()) {
            ifSymbols =
                    new InfFlowProofSymbols(services.getProof()
                            .env().getInitConfig().activatedTaclets());
        }
        addSymbols(l);
    }

    public static String printSymbols() {
        return symbols().printProofSymbols();
    }

    /**
     * Prepare program and location variables.
     * <p/>
     * @author christoph
     * <p/>
     */
    public static class IFProofObligationVars {

        public final ProofObligationVars c1, c2, symbExecVars;

        public final Map<Term, Term> map1, map2;


        public IFProofObligationVars(ProofObligationVars symbExecVars,
                                     Services services, boolean local) {
            this(new ProofObligationVars(symbExecVars, "_A", services, local),
                 new ProofObligationVars(symbExecVars, "_B", services, local),
                 symbExecVars);
        }


        private IFProofObligationVars(ProofObligationVars c1,
                                     ProofObligationVars c2,
                                     ProofObligationVars symbExecVars) {
            this.c1 = c1;
            this.c2 = c2;
            this.symbExecVars = symbExecVars;

            map1 = new HashMap<Term, Term>();
            map2 = new HashMap<Term, Term>();

            if (symbExecVars != null) {
                linkSymbExecVarsToCopies(symbExecVars);
            }
        }


        private void linkSymbExecVarsToCopies(ProofObligationVars symbExecVars) {
            final Iterator<Term> c1It = c1.termList.iterator();
            final Iterator<Term> c2It = c2.termList.iterator();
            for (final Term symbTerm : symbExecVars.termList) {
                final Term c1Term = c1It.next();
                final Term c2Term = c2It.next();
                if (symbTerm != null) {
                    map1.put(symbTerm, c1Term);
                    map2.put(symbTerm, c2Term);
                }
            }
        }


        @Override
        public String toString() {
            return "[" + symbExecVars + "," + c1 + "," + c2 + "]";
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
