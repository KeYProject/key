/*
 * To change this template, choose Tools | Templates and open the template in
 * the editor.
 */
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.init.po.snippet.BasicPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.InfFlowPOSnippetFactory;
import de.uka.ilkd.key.proof.init.po.snippet.POSinppetFactory;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;



/**
 *
 * @author christoph
 */
public class InfFlowContractPO extends AbstractOperationPO implements ContractPO {

    private final InformationFlowContract contract;
    private final ProofObligationVars symbExecVars;
    private final IFProofObligationVars ifVars;


    public InfFlowContractPO(InitConfig initConfig,
                               InformationFlowContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
        
        // generate proof obligation variables
        IProgramMethod pm = contract.getTarget();
        symbExecVars = new ProofObligationVars(pm, contract.getKJT(), services);
        assert (symbExecVars.self == null) == (pm.isStatic());
        ifVars = new IFProofObligationVars(pm, contract.getKJT(), symbExecVars,
                                           services);
    }


    @Override
    public void readProblem() throws ProofInputException {
        // generate snippet factory for symbolic execution
        BasicPOSnippetFactory symbExecFactory =
                POSinppetFactory.getBasicFactory(contract, symbExecVars, services);

        // precondition
        final Term freePre = symbExecFactory.create(BasicPOSnippetFactory.Snippet.FREE_PRE);
        final Term contractPre = symbExecFactory.create(BasicPOSnippetFactory.Snippet.CONTRACT_PRE);
        final Term pre = TB.and(freePre, contractPre);
        
        // symbolic execution
        Term symExec = symbExecFactory.create(BasicPOSnippetFactory.Snippet.SYMBOLIC_EXEC);

        // final symbolic execution term
        Term finalSymbolicExecutionTerm = TB.not(TB.and(pre, symExec));

        // information flow po
        BasicPOSnippetFactory execPredFactory1 =
                POSinppetFactory.getBasicFactory(contract, ifVars.c1, services);
        BasicPOSnippetFactory execPredFactory2 =
                POSinppetFactory.getBasicFactory(contract, ifVars.c2, services);

        final Term exec1 =
                execPredFactory1.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_WITH_PRE_RELATION);
//                buildExecution(ifVars.c1, ifVars.map1, symbExecVars.heap, symbExecGoals);
        final Term exec2 =
                execPredFactory2.create(BasicPOSnippetFactory.Snippet.METHOD_CALL_WITH_PRE_RELATION);
//                buildExecution(ifVars.c2, ifVars.map2, symbExecVars.heap, symbExecGoals);
//        addContractApplicationTaclets(symbExecProof);

        InfFlowPOSnippetFactory f =
                POSinppetFactory.getInfFlowFactory(contract, ifVars.c1,
                                                   ifVars.c2, services);
        Term post = f.create(InfFlowPOSnippetFactory.Snippet.INF_FLOW_POST);

        final Term finalInfFlowTerm = TB.imp(TB.and(exec1, exec2), post);

        // register final terms
        assignPOTerms(finalSymbolicExecutionTerm, finalInfFlowTerm);
        collectClassAxioms(contract.getKJT());
    }


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
        return symbExecVars.mbyAtPre;
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


    
    
    
    private Term buildExecution(ProofObligationVars c,
                                Map<Term, Term> vsMap,
                                Term symbExecHeap,
                                ImmutableList<de.uka.ilkd.key.proof.Goal> symbExecGoals) {
        final Term exec = buildOrNotFormulaFromGoals(symbExecGoals);
        // the build in heap symbol has to be handled with care
        final HashMap<Operator, Boolean> doNotReplace =
                new HashMap<Operator, Boolean>();
        doNotReplace.put(symbExecHeap.op(), Boolean.TRUE);
        final Term renamedExec =
                renameVariablesAndSkolemConstants(exec, vsMap, doNotReplace, c.postfix);
        return TB.applyElementary(services, c.heap, renamedExec);
    }


    private Term[] applyProgramRenamingsToSubs(Term term,
                                               Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
                                               Map<Operator, Boolean> notReplaceMap,
                                               String postfix) {
        Term[] appliedSubs = null;
        if (term.subs() != null) {
            appliedSubs = new Term[term.subs().size()];
            for (int i = 0; i < appliedSubs.length; i++) {
                appliedSubs[i] = applyRenamingsToPrograms(term.sub(i),
                                                          progVarReplaceMap,
                                                          notReplaceMap,
                                                          postfix);
            }
        }
        return appliedSubs;
    }


    private Map<ProgramVariable, ProgramVariable> extractProgamVarReplaceMap(Map<Term, Term> replaceMap) {
        Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
                new HashMap<ProgramVariable, ProgramVariable>();
        for (Term t : replaceMap.keySet()) {
            if (t.op() instanceof ProgramVariable) {
                progVarReplaceMap.put((ProgramVariable)t.op(),
                                      (ProgramVariable)replaceMap.get(t).op());
            }
        }
        return progVarReplaceMap;
    }

    private void insertBoundVarsIntoNotReplaceMap(Term term,
                                                  Map<Operator, Boolean> notReplaceMap) {
        if (term.boundVars() != null) {
            for (QuantifiableVariable bv : term.boundVars()) {
                notReplaceMap.put(bv, Boolean.TRUE);
            }
        }
    }

    private Term renameFormulasWithoutPrograms(Term term,
                                               Map<Term, Term> replaceMap,
                                               Map<Operator, Boolean> notReplaceMap,
                                               String postfix) {
        if (term == null) {
            return null;
        }
        
        if (replaceMap == null) {
            replaceMap = new HashMap<Term, Term>();
        }
        if (notReplaceMap == null) {
            notReplaceMap = new HashMap<Operator, Boolean>();
        }

        if (notReplaceMap.containsKey(term.op())) {
            return term;
        } else if (replaceMap.containsKey(term)) {
            return replaceMap.get(term);
        } else if (term.op() instanceof ParsableVariable) {
            assert term.subs().isEmpty();
            ParsableVariable pv = (ParsableVariable) term.op();
            Name newName =
                    VariableNameProposer.DEFAULT.getNewName(services,
                                                            new Name(pv.name()
                                                                     + postfix));
            Operator renamedPv = pv.rename(newName);
            services.getNamespaces().functions().addSafely(renamedPv);
            Term pvTerm = TermFactory.DEFAULT.createTerm(renamedPv);
            replaceMap.put(term, pvTerm);
            return pvTerm;

        } else if (term.op() instanceof Function
                   && ((Function) term.op()).isSkolemConstant()) {
            Function f = (Function) term.op();
            Name newName =
                    VariableNameProposer.DEFAULT.getNewName(services,
                                                            new Name(f.name()
                                                                     + postfix));
            Function renamedF = f.rename(newName);
            services.getNamespaces().functions().addSafely(renamedF);
            Term fTerm =
                    TermFactory.DEFAULT.createTerm(renamedF);
            replaceMap.put(term, fTerm);
            return fTerm;
        } else if (term.op() instanceof ElementaryUpdate) {
            ElementaryUpdate u = (ElementaryUpdate) term.op();
            Term lhsTerm = TB.var(u.lhs());
            Term renamedLhs = renameFormulasWithoutPrograms(lhsTerm,
                                                                replaceMap,
                                                                notReplaceMap,
                                                                postfix);
            Term[] renamedSubs =
                    renameSubs(term, replaceMap, notReplaceMap, postfix);
            ElementaryUpdate renamedU =
                    ElementaryUpdate.getInstance((UpdateableOperator)renamedLhs.op());
            Term uTerm = TermFactory.DEFAULT.createTerm(renamedU, renamedSubs);
            replaceMap.put(term, uTerm);
            return uTerm;
        } else {
            insertBoundVarsIntoNotReplaceMap(term, notReplaceMap);
            Term[] renamedSubs =
                    renameSubs(term, replaceMap, notReplaceMap, postfix);
            Term renamedTerm =
                    TermFactory.DEFAULT.createTerm(term.op(), renamedSubs,
                                                   term.boundVars(),
                                                   term.javaBlock());
            replaceMap.put(term, renamedTerm);
            return renamedTerm;
        }
    }

    private JavaBlock renameJavaBlock(Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
                                      Term term) {
        ProgVarReplaceVisitor paramRepl =
        new ProgVarReplaceVisitor(term.javaBlock().program(), progVarReplaceMap, services);
        paramRepl.start();
        JavaBlock renamedJavaBlock =
                JavaBlock.createJavaBlock((StatementBlock)paramRepl.result());
        return renamedJavaBlock;
    }



    
    private void addContractApplicationTaclets(Proof symbExecProof) {
        for (Rule r : symbExecProof.env().getRegisteredRules()) {
            if (r instanceof Taclet) {
                Taclet t = (Taclet)r;
                if (t.getSurviveSymbExec()) {
                    taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(t));
                    initConfig.getProofEnv().registerRule(t, AxiomJustification.INSTANCE);
                }
            }
        }
    }

    
    
    
    @Override
    public InformationFlowContract getContract() {
        return (InformationFlowContract) contract;
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


    private Term buildOrNotFormulaFromGoals(ImmutableList<Goal> symbExecGoals) {
        Term result = TB.ff();
        for (Goal symbExecGoal : symbExecGoals) {
            result = TB.or(result, buildNotFormulaFromGoal(symbExecGoal));
        }
        return result;
    }


    private Term buildNotFormulaFromGoal(Goal symbExecGoal) {
        Term result = TB.tt();
        for (SequentFormula f : symbExecGoal.sequent().antecedent()) {
            result = TB.and(result, f.formula());
        }
        for (SequentFormula f : symbExecGoal.sequent().succedent()) {
            result = TB.and(result, TB.not(f.formula()));
        }
        return result;
    }


    private Term renameVariablesAndSkolemConstants(Term term,
                                                   Map<Term, Term> replaceMap,
                                                   Map<Operator, Boolean> notReplaceMap,
                                                   String postfix) {
        Term temp = renameFormulasWithoutPrograms(term, replaceMap,
                                                  notReplaceMap,
                                                  postfix);
        Map<ProgramVariable, ProgramVariable> progVarReplaceMap = extractProgamVarReplaceMap(replaceMap);
        return applyRenamingsToPrograms(temp, progVarReplaceMap, notReplaceMap, postfix);
    }

    
    protected Term applyRenamingsToPrograms(Term term,
                                            Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
                                            Map<Operator, Boolean> notReplaceMap,
                                            String postfix) {
        if (term != null) {
            JavaBlock renamedJavaBlock = renameJavaBlock(progVarReplaceMap, term);
            Term[] appliedSubs = applyProgramRenamingsToSubs(term, progVarReplaceMap,
                                                            notReplaceMap, postfix);

            Term renamedTerm =
                    TermFactory.DEFAULT.createTerm(term.op(), appliedSubs,
                                                    term.boundVars(),
                                                    renamedJavaBlock);
            return renamedTerm;
        } else {
            return null;
        }
    }
    

    private Term[] renameSubs(Term term,
                              Map<Term, Term> replaceMap,
                              Map<Operator, Boolean> notReplaceMap,
                              String postfix) {
        Term[] renamedSubs = null;
        if (term.subs() != null) {
            renamedSubs = new Term[term.subs().size()];
            for (int i = 0; i < renamedSubs.length; i++) {
                renamedSubs[i] = renameFormulasWithoutPrograms(term.sub(i),
                                                               replaceMap,
                                                               notReplaceMap,
                                                               postfix);
            }
        }
        return renamedSubs;
    }


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
     * 
     * @author christoph
     *
     */
    public static class IFProofObligationVars {

        final ProofObligationVars c1, c2;
        final Map<Term, Term> map1, map2;


        public IFProofObligationVars(IProgramMethod pm,
                              KeYJavaType kjt,
                              ProofObligationVars symbExecVars,
                              Services services) {
            this(new ProofObligationVars(pm, kjt, "_A", services),
                 new ProofObligationVars(pm, kjt, "_B", services),
                 pm, kjt, symbExecVars);
        }


        public IFProofObligationVars(ProofObligationVars c1,
                              ProofObligationVars c2,
                              IProgramMethod pm,
                              KeYJavaType kjt,
                              ProofObligationVars symbExecVars) {
            this.c1 = c1;
            this.c2 = c2;

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
    }

    
    // the following code is legacy code
    
    @Override
    @Deprecated
    protected StatementBlock buildOperationBlock(ImmutableList<LocationVariable> formalParVars,
                                                 ProgramVariable selfVar,
                                                 ProgramVariable resultVar) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");
    }


    @Override
    @Deprecated
    protected Term getPre(List<LocationVariable> modHeaps,
                          ProgramVariable selfVar, 
                          ImmutableList<ProgramVariable> paramVars,
                          Map<LocationVariable, LocationVariable> atPreVars, 
                          Services services) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");
    }
    

    @Override
    @Deprecated
    protected Term getPost(List<LocationVariable> modHeaps, 
                           ProgramVariable selfVar, ImmutableList<ProgramVariable> paramVars, 
                           ProgramVariable resultVar, 
                           ProgramVariable exceptionVar, 
                           Map<LocationVariable, LocationVariable> atPreVars, 
                           Services services) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");
    }
    
    
    @Override
    @Deprecated
    protected Term buildFrameClause(List<LocationVariable> modHeaps,
                                    Map<LocationVariable, Map<Term, Term>> heapToAtPre,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");
    }

    
    @Override
    @Deprecated
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");
    }

    
    @Override
    @Deprecated
    protected Term generateMbyAtPreDef(Term selfVar,
                                       ImmutableList<Term> paramVars) {
        throw new UnsupportedOperationException("Not supported any more. "
                + "Please use the POSnippetFactory instead.");
    }

}
