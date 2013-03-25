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
import de.uka.ilkd.key.proof.mgt.SpecificationRepository;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.tacletbuilder.RemovePostTacletBuilder;
import de.uka.ilkd.key.rule.tacletbuilder.SplitPostTacletBuilder;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.speclang.InformationFlowContract;
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


    public InfFlowContractPO(InitConfig initConfig,
                             InformationFlowContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;

        // generate proof obligation variables
        IProgramMethod pm = contract.getTarget();
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
        Term selfComposedExec =
                f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_EXECUTION_WITH_PRE_RELATION);
        Term post =
                f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);
        // register final term, taclets and collect class axioms
        assignPOTerms(TB.imp(selfComposedExec, post));
        collectClassAxioms(contract.getKJT());

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

    /*
    //@Override
    public Term buildProblem(LoopInvariant loopInv, ProofObligationVars appData, Services services)
    throws ProofInputException {
        IFProofObligationVars ifVars = new IFProofObligationVars(appData, services);
        // create proof obligation
        InfFlowPOSnippetFactory f =
            POSnippetFactory.getInfFlowFactory(loopInv, ifVars.c1,
                                               ifVars.c2, services);
        Term selfComposedExec =
            f.create(InfFlowPOSnippetFactory.Snippet.SELFCOMPOSED_LOOP_WITH_INV_RELATION);
        Term post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_INPUT_OUTPUT_RELATION);
        
        // create and add split-post and remove-post taclets
        final SplitPostTacletBuilder splitPostTB = new SplitPostTacletBuilder();
        final ArrayList<Taclet> splitPostTaclets = splitPostTB.generateTaclets(post);
        for (final Taclet t : splitPostTaclets) {
            taclets = taclets.add(NoPosTacletApp.createFixedNoPosTacletApp(t, SVInstantiations.EMPTY_SVINSTANTIATIONS, services));
            initConfig.getProofEnv().registerRule(t, AxiomJustification.INSTANCE);
        }
        final RemovePostTacletBuilder tb = new RemovePostTacletBuilder();
        final ArrayList<Taclet> removePostTaclets = tb.generateTaclets(post);
        for (final Taclet t : removePostTaclets) {
            taclets = taclets.add(NoPosTacletApp.createFixedNoPosTacletApp(t, SVInstantiations.EMPTY_SVINSTANTIATIONS, services));
            initConfig.getProofEnv().registerRule(t, AxiomJustification.INSTANCE);
        }
        
        Term poTerms = TB.imp(selfComposedExec, post);
        return poTerms;
    }*/


    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof InfFlowContractPO)) {
            return false;
        }
        InfFlowContractPO cPO = (InfFlowContractPO) po;
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


//    protected Term buildAbbreviationTaclet(Term replaceWithTerm,
//                                           Name funcName,
//                                           IFProofObligationVars vs) {
//        ImmutableList<ProgramVariable> progVars = collectProgramVaribles(vs);
//        ImmutableList<Sort> sorts = collectVaribleSorts(progVars);
//        Term[] terms = collectVariableTerms(progVars);
//
//        Function func =
//                new Function(funcName, Sort.FORMULA,
//                             sorts.toArray(new Sort[sorts.size()]));
//        register(func);
//
//        TacletGenerator TG = TacletGenerator.getInstance();
//        Name tacletName = MiscTools.toValidTacletName(funcName.toString()
//                                                      + "_axiom");
//        Term findTerm = TB.func(func, terms);
//        Name ruleSetName = new Name("useHiddenAxiom");
//        RuleSet ruleSet = (RuleSet) services.getNamespaces().lookup(ruleSetName);
//        Taclet t = TG.generateRewriteTaclet(tacletName, findTerm,
//                                            replaceWithTerm, progVars,
//                                            ruleSet, services);
//        register(t);
//        return findTerm;
//    }
//    private ImmutableList<ProgramVariable> collectProgramVaribles(
//            IFProofObligationVars vs) {
//        ImmutableList<ProgramVariable> progVars =
//                ImmutableSLList.<ProgramVariable>nil();
//        progVars = progVars.append(vs.c1.selfVar);
//        progVars = progVars.append(vs.c1.heapAtPreVar);
//        progVars = progVars.append(vs.c1.heapAtPostVar);
//        if (vs.c1.resultVar != null) {
//            progVars = progVars.append(vs.c1.resultVar);
//        }
//        progVars = progVars.append(vs.c1.paramVars);
//        progVars = progVars.append(vs.c2.selfVar);
//        progVars = progVars.append(vs.c2.heapAtPreVar);
//        progVars = progVars.append(vs.c2.heapAtPostVar);
//        if (vs.c2.resultVar != null) {
//            progVars = progVars.append(vs.c2.resultVar);
//        }
//        progVars = progVars.append(vs.c2.paramVars);
//        return progVars;
//    }
//    private ImmutableList<Sort> collectVaribleSorts(
//            ImmutableList<ProgramVariable> progVars) {
//        ImmutableList<Sort> sorts =
//                ImmutableSLList.<Sort>nil();
//        for (ProgramVariable progVar : progVars) {
//            sorts = sorts.append(progVar.getKeYJavaType().getSort());
//        }
//        return sorts;
//    }
//    private Term[] collectVariableTerms(ImmutableList<ProgramVariable> progVars) {
//        Term[] terms = new Term[progVars.size()];
//        int i = 0;
//        for (ProgramVariable progVar : progVars) {
//            terms[i] = TB.var(progVar);
//            i++;
//        }
//        return terms;
//    }
//
//    
//    private void register(Taclet axiomTaclet) {
//        assert axiomTaclet != null : "Proof obligation generation generated null taclet.";
//        taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(axiomTaclet));
//        initConfig.getProofEnv().registerRule(axiomTaclet,
//                                              AxiomJustification.INSTANCE);
//    }
//    public static Term buildContractApplication(
//            LoopInvariant targetContracts,
//            LoopInvariantApplicationData contAppData,
//            LoopInvariantApplicationData contAppData2,
//            Services services) {
//        ProofObligationVars targetC1 =
//                new ProofObligationVars((ProgramMethod) target.obs,
//                                        target.kjt,
//                                        contAppData.self,
//                                        contAppData.self,
//                                        contAppData.params,
//                                        contAppData.result,
//                                        contAppData.result,
//                                        contAppData.heapAtPre,
//                                        contAppData.heapAtPre,
//                                        contAppData.heapAtPost, false,
//                                        "", services, false);
//        ProofObligationVars targetC2 =
//                new ProofObligationVars((ProgramMethod) target.obs,
//                                        target.kjt,
//                                        contAppData2.self,
//                                        contAppData2.self,
//                                        contAppData2.params,
//                                        contAppData2.result,
//                                        contAppData2.result,
//                                        contAppData2.heapAtPre,
//                                        contAppData2.heapAtPre,
//                                        contAppData2.heapAtPost, false,
//                                        "", services, false);
//        final IFProofObligationVars targetVs =
//                new IFProofObligationVars(targetC1, targetC2,
//                                          cont.getTarget(), cont.getKJT(),
//                                          null, null);
//
//        Term preCond1 = cont.getPre(contAppData.heapAtPre, contAppData.self,
//                contAppData.params, null, services);
//        Term preCond2 = cont.getPre(contAppData2.heapAtPre,
//                contAppData2.self, contAppData2.params, null,
//                services);
//
//        Term inOutRelations = buildInputOutputRelations(cont, targetVs, services);
//        return TB.imp(TB.and(preCond1, preCond2), inOutRelations);
//    }
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
            Iterator<Term> c1It = c1.termList.iterator();
            Iterator<Term> c2It = c2.termList.iterator();
            for (Term symbTerm : symbExecVars.termList) {
                Term c1Term = c1It.next();
                Term c2Term = c2It.next();
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
