// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.proof.mgt.AxiomJustification;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.speclang.InformationFlowContract;
import java.util.*;



/**
 * The proof obligation for dependency contracts. 
 */
public final class InformationFlowContractPO extends AbstractOperationPO implements ContractPO {

    private InformationFlowContract contract;
    protected Term mbyAtPre;

    public InformationFlowContractPO(
            InitConfig initConfig,
            InformationFlowContract contract) {
        super(initConfig, contract.getName());
        this.contract = contract;
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


    private static Term buildInputRelation(InformationFlowContract contract,
                                           IFProofObligationVars vs,
                                           ImmutableList<Term> referenceLocSet1,
                                           ImmutableList<Term> referenceLocSet2,
                                           ImmutableList<ImmutableList<Term>> declassClause1,
                                           ImmutableList<ImmutableList<Term>> declassClause2,
                                           Services services) {
        final Term mainInputEqRelation =
                buildMainInputEqualsRelation(contract, referenceLocSet1,
                                             referenceLocSet2, vs, services);
        final ImmutableList<Term> declassifiesRelations =
                buildDeclassifiesRelations(referenceLocSet1, declassClause1,
                                         referenceLocSet2, declassClause2,
                                         services);

        ImmutableList<Term> inputRelations =
                ImmutableSLList.<Term>nil();
        inputRelations = inputRelations.append(mainInputEqRelation);
        inputRelations = inputRelations.append(declassifiesRelations);

        return TB.and(inputRelations);
    }


    private static Term buildOutputRelation(InformationFlowContract contract,
                                            IFProofObligationVars vs,
                                            ImmutableList<Term> referenceLocSet1,
                                            ImmutableList<Term> referenceLocSet2,
                                            Services services) {
        Term mainEqRelation =
                buildMainOutputEqualsRelation(contract, referenceLocSet1,
                                              referenceLocSet2, vs, services);
        ImmutableList<Term> outputRelations = ImmutableSLList.<Term>nil();
        outputRelations = outputRelations.append(mainEqRelation);
        return TB.and(outputRelations);
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


    private static Term buildInputOutputRelations(InformationFlowContract contract,
                                                  IFProofObligationVars vs,
                                                  Services services) {
        ImmutableList<ImmutableList<Term>> respectsAtPre1 =
                contract.getRespects(vs.c1.heapAtPre, vs.c1.self, vs.c1.params,
                                     vs.c1.resultAtPost, services);
        ImmutableList<ImmutableList<Term>> respectsAtPre2 =
                contract.getRespects(vs.c2.heapAtPre, vs.c2.self, vs.c2.params,
                                     vs.c2.resultAtPost, services);
        ImmutableList<ImmutableList<Term>> respectsAtPost1 =
                contract.getRespects(vs.c1.heapAtPost, vs.c1.selfAtPost, vs.c1.params,
                                     vs.c1.resultAtPost, services);
        ImmutableList<ImmutableList<Term>> respectsAtPost2 =
                contract.getRespects(vs.c2.heapAtPost, vs.c2.selfAtPost, vs.c2.params,
                                     vs.c2.resultAtPost, services);


        ImmutableList<ImmutableList<Term>> declassClause1 =
                contract.getDeclassifies(vs.c1.heapAtPre, vs.c1.self, vs.c1.params,
                                       vs.c1.resultAtPost, services);
        ImmutableList<ImmutableList<Term>> declassClause2 =
                contract.getDeclassifies(vs.c2.heapAtPre, vs.c2.self, vs.c2.params,
                                       vs.c2.resultAtPost, services);

        ImmutableList<Term> inputOutputRelations = ImmutableSLList.<Term>nil();

        Iterator<ImmutableList<Term>> respectsAtPre2It = respectsAtPre2.iterator();
        Iterator<ImmutableList<Term>> respectsAtPost1It = respectsAtPost1.iterator();
        Iterator<ImmutableList<Term>> respectsAtPost2It = respectsAtPost2.iterator();
        for (ImmutableList<Term> referenceLocSetAtPre1 : respectsAtPre1) {
            ImmutableList<Term> referenceLocSetAtPre2 = respectsAtPre2It.next();
            ImmutableList<Term> referenceLocSetAtPost1 = respectsAtPost1It.next();
            ImmutableList<Term> referenceLocSetAtPost2 = respectsAtPost2It.next();
            Term inputOutputRelation =
                    buildInputOutputRelation(contract, referenceLocSetAtPre1,
                                             referenceLocSetAtPre2,
                                             referenceLocSetAtPost1,
                                             referenceLocSetAtPost2,
                                             declassClause1,
                                             declassClause2, vs, services);
            inputOutputRelations =
                    inputOutputRelations.append(inputOutputRelation);
        }

        return TB.and(inputOutputRelations);
    }


    private static Term buildInputOutputRelation(InformationFlowContract contract,
                                                 ImmutableList<Term> referenceLocSetAtPre1,
                                                 ImmutableList<Term> referenceLocSetAtPre2,
                                                 ImmutableList<Term> referenceLocSetAtPost1,
                                                 ImmutableList<Term> referenceLocSetAtPost2,
                                                 ImmutableList<ImmutableList<Term>> declassClause1,
                                                 ImmutableList<ImmutableList<Term>> declassClause2,
                                                 IFProofObligationVars vs,
                                                 Services services) {
        Term inputRelation =
                buildInputRelation(contract, vs, referenceLocSetAtPre1,
                                   referenceLocSetAtPre2, declassClause1,
                                   declassClause2, services);
        Term outputRelation =
                buildOutputRelation(contract, vs, referenceLocSetAtPost1,
                                    referenceLocSetAtPost2, services);

        return TB.imp(inputRelation, outputRelation);
    }


    private static Term buildMainInputEqualsRelation(InformationFlowContract contract,
                                                     ImmutableList<Term> referenceLocSet1,
                                                     ImmutableList<Term> referenceLocSet2,
                                                     IFProofObligationVars vs,
                                                     Services services) {
        Term framingLocs1 =
                contract.getDep(vs.c1.heapAtPre, vs.c1.self, vs.c1.params,
                                services);
        Term framingLocs2 =
                contract.getDep(vs.c2.heapAtPre, vs.c2.self, vs.c2.params,
                                services);
        Term[] eqAtLocs = new Term[referenceLocSet1.size()];
        Iterator<Term> refLoc1It = referenceLocSet1.iterator();
        Iterator<Term> refLoc2It = referenceLocSet2.iterator();
        for(int i=0; i < eqAtLocs.length; i++) {
            Term refLoc1Term = refLoc1It.next();
            Term refLoc2Term = refLoc2It.next();
//            // hack ?
//            if(refLoc1Term.sort().name().equals(services.getTypeConverter().getLocSetLDT().name())) {
//                eqAtLocs[i] = TB.eqAtLocs(services,
//                                vs.c1.heapAtPre,
//                                TB.intersect(services, refLoc1Term,
//                                             framingLocs1),
//                                vs.c2.heapAtPre,
//                                TB.intersect(services, refLoc2Term,
//                                             framingLocs2));
//            } else {
                SearchVisitor search = new SearchVisitor(vs.c1.resultAtPost);
                refLoc1Term.execPreOrder(search);
                if (!search.termFound) {
                    // refLocTerms which contain \result are not included in
                    // the precondition
                    eqAtLocs[i] = TB.equals(refLoc1Term, refLoc2Term);
                } else {
                    eqAtLocs[i] = TB.tt();
                }
//            }
        }
        return TB.and(eqAtLocs);
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

    @Override
    protected IProgramMethod getProgramMethod() {
        return contract.getTarget();
    }

    @Override
    protected boolean isTransactionApplicable() {
        return false;
    }

    @Override
    protected KeYJavaType getCalleeKeYJavaType() {
        return contract.getKJT();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected StatementBlock buildOperationBlock(ImmutableList<LocationVariable> formalParVars,
                                                 ProgramVariable selfVar,
                                                 ProgramVariable resultVar) {
       final ImmutableArray<Expression> formalArray = new ImmutableArray<Expression>(formalParVars.toArray(
             new ProgramVariable[formalParVars.size()]));

       if (getContract().getTarget().isConstructor()) {
            assert selfVar != null;
            assert resultVar == null;
            final Expression[] formalArray2 = formalArray.toArray(
                    new Expression[formalArray.size()]);
            final New n = new New(formalArray2, new TypeRef(
                    getContract().getKJT()), null);
            final CopyAssignment ca = new CopyAssignment(selfVar, n);
            return new StatementBlock(ca);
        } else {
            final MethodBodyStatement call =
                    new MethodBodyStatement(getContract().getTarget(),
                                            selfVar,
                                            resultVar,
                                            formalArray);
            return new StatementBlock(call);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Term generateMbyAtPreDef(ProgramVariable selfVar,
                                       ImmutableList<ProgramVariable> paramVars) {
        final Term mbyAtPreDef;
        if (contract.hasMby()) {
            final Function mbyAtPreFunc =
                    new Function(new Name(TB.newName(services, "mbyAtPre")),
                                 services.getTypeConverter().getIntegerLDT().targetSort());
            register(mbyAtPreFunc);
            mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby = contract.getMby(selfVar, paramVars, services);
            mbyAtPreDef = TB.equals(mbyAtPre, mby);
        } else {
            mbyAtPreDef = TB.tt();
        }
        return mbyAtPreDef;
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    protected Term generateMbyAtPreDef(Term selfVar,
                                       ImmutableList<Term> paramVars) {
        final Term mbyAtPreDef;
        if (contract.hasMby()) {
            final Function mbyAtPreFunc =
                    new Function(new Name(TB.newName(services, "mbyAtPre")),
                                 services.getTypeConverter().getIntegerLDT().targetSort());
            register(mbyAtPreFunc);
            mbyAtPre = TB.func(mbyAtPreFunc);
            final Term mby = contract.getMby(TB.getBaseHeap(services), selfVar, paramVars, services);
            mbyAtPreDef = TB.equals(mbyAtPre, mby);
        } else {
            mbyAtPreDef = TB.tt();
        }
        return mbyAtPreDef;
    }
    
    @Override
    protected Term getPre(List<LocationVariable> modHeaps,
                          ProgramVariable selfVar,
                          ImmutableList<ProgramVariable> paramVars,
                          Map<LocationVariable, LocationVariable> atPreVars,
                          Services services) {
        return contract.getPre(modHeaps, selfVar, paramVars, atPreVars, services);
    }

    @Override
    protected Term getPost(List<LocationVariable> modHeaps,
                           ProgramVariable selfVar,
                           ImmutableList<ProgramVariable> paramVars,
                           ProgramVariable resultVar,
                           ProgramVariable exceptionVar,
                           Map<LocationVariable, LocationVariable> atPreVars,
                           Services services) {
        return TB.tt();
    }

    @Override
    protected Term buildFrameClause(List<LocationVariable> modHeaps,
                                    Map<LocationVariable, Map<Term, Term>> heapToAtPre,
                                    ProgramVariable selfVar,
                                    ImmutableList<ProgramVariable> paramVars) {
        return TB.tt();
    }

    @Override
    protected Modality getTerminationMarker() {
        return getContract().getModality();
    }

    @Override
    protected String buildPOName(boolean transactionFlag) {
        return getContract().getName();
    }

    private static class SearchVisitor extends Visitor {
        private boolean termFound = false;
        private Term searchTerm;

        public SearchVisitor(Term searchTerm) {
            this.searchTerm = searchTerm;
        }
        
        public boolean containsTerm() {
            return termFound;
        }

        @Override
        public void visit(Term visited) {
            termFound = termFound || visited.equals(searchTerm);
        }
    }

    private static Term buildMainOutputEqualsRelation(InformationFlowContract contract,
                                                      ImmutableList<Term> referenceLocSet1,
                                                      ImmutableList<Term> referenceLocSet2,
                                                      IFProofObligationVars vs,
                                                      Services services) {
        Term framingLocs1 =
                contract.getMod(vs.c1.heapAtPost, vs.c1.selfAtPost, vs.c1.params,
                                services);
        Term framingLocs2 =
                contract.getMod(vs.c2.heapAtPost, vs.c2.selfAtPost, vs.c2.params,
                                services);
        Term[] eqAtLocs = new Term[referenceLocSet1.size()];
        Iterator<Term> refLoc1It = referenceLocSet1.iterator();
        Iterator<Term> refLoc2It = referenceLocSet2.iterator();
        for(int i=0; i < eqAtLocs.length; i++) {
            Term refLoc1Term = refLoc1It.next();
            Term refLoc2Term = refLoc2It.next();
            // TOTO: hack ?
//            if(refLoc1Term.sort().name().equals(services.getTypeConverter().getLocSetLDT().name())) {
//                eqAtLocs[i] = TB.eqAtLocsPost(services,
//                                    vs.c1.heapAtPre,
//                                    vs.c1.heapAtPost,
//                                    TB.intersect(services, refLoc1Term,
//                                                 framingLocs1),
//                                    vs.c2.heapAtPre,
//                                    vs.c2.heapAtPost,
//                                    TB.intersect(services, refLoc2Term,
//                                                 framingLocs2));
//            } else {
            eqAtLocs[i] = TB.equals(refLoc1Term, refLoc2Term);
//            }
        }
        return TB.and(eqAtLocs);
    }


    private static ImmutableList<Term> buildDeclassifiesRelations(
            ImmutableList<Term> referenceLocSet1,
            ImmutableList<ImmutableList<Term>> declassClause1,
            ImmutableList<Term> referenceLocSet2,
            ImmutableList<ImmutableList<Term>> declassClause2,
            Services services) {
        Iterator<ImmutableList<Term>> declassClause2It =
                declassClause2.iterator();
        ImmutableList<Term> declassifications = ImmutableSLList.<Term>nil();
        for (ImmutableList<Term> declassification1 : declassClause1) {
            ImmutableList<Term> declassification2 = declassClause2It.next();
            Term declTerm =
                    buildDeclassifiesRelation(referenceLocSet1, declassification1,
                                            referenceLocSet2, declassification2,
                                            services);
            declassifications = declassifications.append(declTerm);
        }
        return declassifications;
    }


    private static Term buildDeclassifiesRelation(ImmutableList<Term> referenceLocSet1,
                                                ImmutableList<Term> declassClause1,
                                                ImmutableList<Term> referenceLocSet2,
                                                ImmutableList<Term> declassClause2,
                                                Services services) {
        final Term declassification1 = declassClause1.head();
        final Term from1 = declassClause1.tail().head();
        final Term to1 = declassClause1.tail().tail().head();
        final Term ifTerm1 = declassClause1.tail().tail().tail().head();

        final Term declassification2 = declassClause2.head();
        final Term from2 = declassClause2.tail().head();
        final Term to2 = declassClause2.tail().tail().head();
        final Term ifTerm2 = declassClause2.tail().tail().tail().head();

        Term eqTerm = TB.equals(declassification1, declassification2);

        Term condition = TB.tt();
        if (ifTerm1 != null) {
            condition = TB.and(ifTerm1, ifTerm2);
        }
        if (to1 != null) {
            condition = TB.and(TB.equals(to1, TB.seq(services, referenceLocSet1)),
                               TB.equals(to2, TB.seq(services, referenceLocSet2)),
                               condition);
        }
        if (from1 != null) {
            // TODO: to be implemented
        }

        return TB.imp(condition, eqTerm);
    }


    //-------------------------------------------------------------------------
    //public interface
    //-------------------------------------------------------------------------        
    @Override
    public void readProblem()
            throws ProofInputException {
        final SymbolicExecutionPO symbExecPO = getSymbolicExecutionPO();
        final ProofObligationVars symbExecVS =
                symbExecPO.getProofObligationVariables();
        final Proof symbExecProof = getSymbolicExecutionProof(symbExecPO);
        final ImmutableList<Goal> symbExecGoals = symbExecProof.openGoals();
        final IFProofObligationVars vs =
                buildProofObligationVars(symbExecVS, symbExecProof);


        final Term exec1 =
                buildExecution(vs.c1, vs.map1, symbExecVS.heap, symbExecGoals);
        final Term exec2 =
                buildExecution(vs.c2, vs.map2, symbExecVS.heap, symbExecGoals);
        addContractApplicationTaclets(symbExecProof);
        Term post = buildInputOutputRelations(getContract(), vs, services);

        assignPOTerms(TB.imp(TB.and(exec1, exec2), post));
        collectClassAxioms(contract.getKJT());
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

    
    private IFProofObligationVars buildProofObligationVars(
            final ProofObligationVars symbExecVS,
            Proof proof) {
        final IProgramMethod pm = getContract().getTarget();
        final IFProofObligationVars vs =
                new IFProofObligationVars(pm, contract.getKJT(), symbExecVS,
                proof, services);
        return vs;
    }


    private Proof getSymbolicExecutionProof(SymbolicExecutionPO symbExecPO) {
        ImmutableSet<Proof> symbExecProofs =
                services.getSpecificationRepository().getProofs(symbExecPO);
        assert symbExecProofs.size() == 1 : "expect that there is only one proof"
                                            + " for the symbolic execution";
        Proof symbExecProof = symbExecProofs.iterator().next();
        return symbExecProof;
    }


    private SymbolicExecutionPO getSymbolicExecutionPO() {
        SymbolicExecutionPO symbExecPO =
                (SymbolicExecutionPO) getContract().getSymbExecData(services).getProofObl(
                services);
        assert symbExecPO != null : "expect that the symbolic execution contract"
                                    + " has already been generated";
        return symbExecPO;
    }
    
    
    @Override
    public boolean implies(ProofOblInput po) {
        if (!(po instanceof InformationFlowContractPO)) {
            return false;
        }
        InformationFlowContractPO cPO = (InformationFlowContractPO) po;
        return contract.equals(cPO.contract);
    }


    @Override
    public InformationFlowContract getContract() {
        return (InformationFlowContract) contract;
    }


    @Override
    public Term getMbyAtPre() {
        return mbyAtPre;
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
    protected void register(Taclet axiomTaclet) {
        assert axiomTaclet != null : "Proof obligation generation generated null taclet.";
        taclets = taclets.add(NoPosTacletApp.createNoPosTacletApp(axiomTaclet));
        initConfig.getProofEnv().registerRule(axiomTaclet,
                                              AxiomJustification.INSTANCE);
    }


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


    public static Term buildContractApplications(
            ObserverWithType target,
            ImmutableSet<InformationFlowContract> targetContracts,
            ContractApplicationData contAppData,
            ContractApplicationData contAppData2,
            Services services) {
        ImmutableList<Term> contractsApplications = ImmutableSLList.<Term>nil();
        for (InformationFlowContract cont : targetContracts) {
            contractsApplications = contractsApplications.append(
                    buildContractApplication(target, cont, contAppData,
                    contAppData2, services));
        }
        return TB.and(contractsApplications);
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
    
    
    private static Term buildContractApplication(ObserverWithType target,
                                          InformationFlowContract cont,
                                          ContractApplicationData contAppData,
                                          ContractApplicationData contAppData2,
                                          Services services) {
        ProofObligationVars targetC1 =
                new ProofObligationVars((ProgramMethod) target.obs,
                                        target.kjt,
                                        contAppData.self,
                                        contAppData.self,
                                        contAppData.params,
                                        contAppData.result,
                                        contAppData.result,
                                        contAppData.heapAtPre,
                                        contAppData.heapAtPre,
                                        contAppData.heapAtPost,
                                        "", services, false);
        ProofObligationVars targetC2 =
                new ProofObligationVars((ProgramMethod) target.obs,
                                        target.kjt,
                                        contAppData2.self,
                                        contAppData2.self,
                                        contAppData2.params,
                                        contAppData2.result,
                                        contAppData2.result,
                                        contAppData2.heapAtPre,
                                        contAppData2.heapAtPre,
                                        contAppData2.heapAtPost,
                                        "", services, false);
        final IFProofObligationVars targetVs =
                new IFProofObligationVars(targetC1, targetC2,
                                          cont.getTarget(), cont.getKJT(),
                                          null, null);

        Term preCond1 = cont.getPre(contAppData.heapAtPre, contAppData.self,
                contAppData.params, services);
        Term preCond2 = cont.getPre(contAppData2.heapAtPre,
                contAppData2.self, contAppData2.params, services);

        Term inOutRelations = buildInputOutputRelations(cont, targetVs, services);
        return TB.imp(TB.and(preCond1, preCond2), inOutRelations);
    }
    

    /**
     * Prepare program and location variables.
     * 
     * @author christoph
     *
     */
    protected static class IFProofObligationVars {

        final ProofObligationVars c1, c2;
        final Map<Term, Term> map1, map2;


        IFProofObligationVars(IProgramMethod pm,
                              KeYJavaType kjt,
                              ProofObligationVars symbExecVars,
                              Proof proof,
                              Services services) {
            this(new ProofObligationVars(pm, kjt, "_A", services),
                 new ProofObligationVars(pm, kjt, "_B", services),
                 pm, kjt, symbExecVars, proof);
        }


        IFProofObligationVars(ProofObligationVars c1,
                              ProofObligationVars c2,
                              IProgramMethod pm,
                              KeYJavaType kjt,
                              ProofObligationVars symbExecVars,
                              Proof proof) {
            this.c1 = c1;
            this.c2 = c2;

            map1 = new HashMap<Term, Term>();
            map2 = new HashMap<Term, Term>();
            
            if (symbExecVars != null && proof != null) {
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
}
