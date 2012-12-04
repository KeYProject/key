/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.ElementaryUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.UpdateableOperator;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.VariableNameProposer;
import de.uka.ilkd.key.proof.init.InfFlowContractPO.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import java.util.HashMap;
import java.util.Map;


/**
 *
 * @author christoph
 */
abstract class AbstractFinishAuxiliaryComputationMacro implements ProofMacro {

    static final TermBuilder TB = TermBuilder.DF;


    @Override
    public String getName() {
        return "Finish auxiliray computation";
    }


    @Override
    public String getDescription() {
        return "Finish auxiliray computation.";
    }


    protected Term calculateResultingTerm(Proof proof,
                                          IFProofObligationVars ifVars,
                                          Services services) {
        Term[] goalFormulas1 =
                buildExecution(ifVars.c1, ifVars.map1, ifVars.symbExecVars.heap,
                               proof.openGoals(), services);
        Term[] goalFormulas2 =
                buildExecution(ifVars.c2, ifVars.map2, ifVars.symbExecVars.heap,
                               proof.openGoals(), services);

        Term composedStates = TB.ff();
        for (int i = 0; i < goalFormulas1.length; i++) {
            for (int j = i; j < goalFormulas2.length; j++) {
                Term composedState = TB.and(goalFormulas1[i], goalFormulas2[j]);
                composedStates = TB.or(composedStates, composedState);
            }
        }
        return composedStates;
//        return TB.and(TB.or(goalFormulas1), TB.or(goalFormulas2));
    }


    private Term[] buildExecution(ProofObligationVars c,
                                  Map<Term, Term> vsMap,
                                  Term symbExecHeap,
                                  ImmutableList<de.uka.ilkd.key.proof.Goal> symbExecGoals,
                                  Services services) {
        final Term[] goalFormulas = buildFormulasFromGoals(symbExecGoals);
        // the build in heap symbol has to be handled with care
        final HashMap<Operator, Boolean> doNotReplace =
                new HashMap<Operator, Boolean>();
        doNotReplace.put(symbExecHeap.op(), Boolean.TRUE);
        final Term[] renamedGoalFormulas =
                renameVariablesAndSkolemConstants(goalFormulas, vsMap, doNotReplace,
                                                  c.postfix, services);
        Term[] result = new Term[renamedGoalFormulas.length];
        for (int i = 0; i < renamedGoalFormulas.length; i++) {
            result[i] =
                    TB.applyElementary(services, c.heap, renamedGoalFormulas[i]);
        }
        return result;
    }


    private Term[] applyProgramRenamingsToSubs(Term term,
                                               Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
                                               Map<Operator, Boolean> notReplaceMap,
                                               String postfix,
                                               Services services) {
        Term[] appliedSubs = null;
        if (term.subs() != null) {
            appliedSubs = new Term[term.subs().size()];
            for (int i = 0; i < appliedSubs.length; i++) {
                appliedSubs[i] = applyRenamingsToPrograms(term.sub(i),
                                                          progVarReplaceMap,
                                                          notReplaceMap,
                                                          postfix,
                                                          services);
            }
        }
        return appliedSubs;
    }


    private Map<ProgramVariable, ProgramVariable> extractProgamVarReplaceMap(
            Map<Term, Term> replaceMap) {
        Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
                new HashMap<ProgramVariable, ProgramVariable>();
        for (Term t : replaceMap.keySet()) {
            if (t.op() instanceof ProgramVariable) {
                progVarReplaceMap.put((ProgramVariable) t.op(),
                                      (ProgramVariable) replaceMap.get(t).op());
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
                                               String postfix,
                                               Services services) {
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
                                                            new Name(pv.name() +
                                                                     postfix));
            Operator renamedPv = pv.rename(newName);
            services.getNamespaces().programVariables().addSafely(renamedPv);
            Term pvTerm = TermFactory.DEFAULT.createTerm(renamedPv);
            replaceMap.put(term, pvTerm);
            return pvTerm;

        } else if (term.op() instanceof Function &&
                   ((Function) term.op()).isSkolemConstant()) {
            Function f = (Function) term.op();
            Name newName =
                    VariableNameProposer.DEFAULT.getNewName(services,
                                                            new Name(f.name() +
                                                                     postfix));
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
                                                            postfix,
                                                            services);
            Term[] renamedSubs =
                    renameSubs(term, replaceMap, notReplaceMap, postfix, services);
            ElementaryUpdate renamedU =
                    ElementaryUpdate.getInstance((UpdateableOperator) renamedLhs.op());
            Term uTerm = TermFactory.DEFAULT.createTerm(renamedU, renamedSubs);
            replaceMap.put(term, uTerm);
            return uTerm;
        } else {
            insertBoundVarsIntoNotReplaceMap(term, notReplaceMap);
            Term[] renamedSubs =
                    renameSubs(term, replaceMap, notReplaceMap, postfix, services);
            Term renamedTerm =
                    TermFactory.DEFAULT.createTerm(term.op(), renamedSubs,
                                                   term.boundVars(),
                                                   term.javaBlock());
            replaceMap.put(term, renamedTerm);
            return renamedTerm;
        }
    }


    private JavaBlock renameJavaBlock(
            Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
            Term term,
            Services services) {
        ProgVarReplaceVisitor paramRepl =
                new ProgVarReplaceVisitor(term.javaBlock().program(), progVarReplaceMap, services);
        paramRepl.start();
        JavaBlock renamedJavaBlock =
                JavaBlock.createJavaBlock((StatementBlock) paramRepl.result());
        return renamedJavaBlock;
    }


    private Term[] buildFormulasFromGoals(ImmutableList<Goal> symbExecGoals) {
        Term[] result = new Term[symbExecGoals.size()];
        int i = 0;
        for (Goal symbExecGoal : symbExecGoals) {
            result[i] = buildFormulaFromGoal(symbExecGoal);
            i++;
        }
        return result;
    }


    private Term buildFormulaFromGoal(Goal symbExecGoal) {
        Term result = TB.tt();
        for (SequentFormula f : symbExecGoal.sequent().antecedent()) {
            result = TB.and(result, f.formula());
        }
        for (SequentFormula f : symbExecGoal.sequent().succedent()) {
            result = TB.and(result, TB.not(f.formula()));
        }
        return result;
    }


    private Term[] renameVariablesAndSkolemConstants(Term[] terms,
                                                     Map<Term, Term> replaceMap,
                                                     Map<Operator, Boolean> notReplaceMap,
                                                     String postfix,
                                                     Services services) {
        Term[] result = new Term[terms.length];
        for (int i = 0; i < terms.length; i++) {
            result[i] =
                    renameVariablesAndSkolemConstants(terms[i], replaceMap,
                                                      notReplaceMap, postfix,
                                                      services);
        }
        return result;
    }


    private Term renameVariablesAndSkolemConstants(Term term,
                                                   Map<Term, Term> replaceMap,
                                                   Map<Operator, Boolean> notReplaceMap,
                                                   String postfix,
                                                   Services services) {
        Term temp = renameFormulasWithoutPrograms(term, replaceMap,
                                                  notReplaceMap,
                                                  postfix,
                                                  services);
        Map<ProgramVariable, ProgramVariable> progVarReplaceMap =
                extractProgamVarReplaceMap(replaceMap);
        return applyRenamingsToPrograms(temp, progVarReplaceMap, notReplaceMap,
                                        postfix, services);
    }


    protected Term applyRenamingsToPrograms(Term term,
                                            Map<ProgramVariable, ProgramVariable> progVarReplaceMap,
                                            Map<Operator, Boolean> notReplaceMap,
                                            String postfix,
                                            Services services) {
        if (term != null) {
            JavaBlock renamedJavaBlock =
                    renameJavaBlock(progVarReplaceMap, term, services);
            Term[] appliedSubs =
                    applyProgramRenamingsToSubs(term, progVarReplaceMap,
                                                notReplaceMap, postfix,
                                                services);

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
                              String postfix,
                              Services services) {
        Term[] renamedSubs = null;
        if (term.subs() != null) {
            renamedSubs = new Term[term.subs().size()];
            for (int i = 0; i < renamedSubs.length; i++) {
                renamedSubs[i] = renameFormulasWithoutPrograms(term.sub(i),
                                                               replaceMap,
                                                               notReplaceMap,
                                                               postfix,
                                                               services);
            }
        }
        return renamedSubs;
    }


    void addContractApplicationTaclets(Goal initiatingGoal,
                                       Proof symbExecProof) {
        ImmutableList<Goal> openGoals = symbExecProof.openGoals();
        for (Goal openGoal : openGoals) {
            ImmutableSet<NoPosTacletApp> ruleApps =
                    openGoal.indexOfTaclets().allNoPosTacletApps();
            for (NoPosTacletApp ruleApp : ruleApps) {
                Taclet t = ruleApp.taclet();
                if (t.getSurviveSymbExec()) {
                    initiatingGoal.addTaclet(t, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
                }
            }
        }
    }
}
