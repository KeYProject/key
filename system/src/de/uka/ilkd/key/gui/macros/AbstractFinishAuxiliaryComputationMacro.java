/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */
package de.uka.ilkd.key.gui.macros;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.IFProofObligationVars;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.InfFlowProgVarRenamer;

import java.util.Map;


/**
 *
 * @author christoph
 */
abstract class AbstractFinishAuxiliaryComputationMacro implements ProofMacro {

    static final TermBuilder TB = TermBuilder.DF;

    @Override
    public String getName() {
        return "Finish auxiliary computation";
    }


    @Override
    public String getDescription() {
        return "Finish auxiliary computation.";
    }


    static Term calculateResultingTerm(Proof proof,
                                               IFProofObligationVars ifVars,
                                               Goal initGoal) {
        final Term[] goalFormulas1 =
                buildExecution(ifVars.c1, ifVars.getMapFor(ifVars.c1),
                               proof.openGoals(), initGoal);
        final Term[] goalFormulas2 =
                buildExecution(ifVars.c2, ifVars.getMapFor(ifVars.c2),
                               proof.openGoals(), initGoal);

        Term composedStates = TB.ff();
        for (int i = 0; i < goalFormulas1.length; i++) {
            for (int j = i; j < goalFormulas2.length; j++) {
                final Term composedState = TB.and(goalFormulas1[i], goalFormulas2[j]);
                composedStates = TB.or(composedStates, composedState);
            }
        }
        return composedStates;
    }


    private static Term[] buildExecution(ProofObligationVars c,
                                         Map<Term, Term> vsMap,
                                         ImmutableList<de.uka.ilkd.key.proof.Goal> symbExecGoals,
                                         Goal initGoal) {
        Services services = initGoal.proof().getServices();
        final Term[] goalFormulas = buildFormulasFromGoals(symbExecGoals);
        final InfFlowProgVarRenamer renamer =
                        new InfFlowProgVarRenamer(goalFormulas, vsMap,
                                                  c.postfix, initGoal, services);
        final Term[] renamedGoalFormulas =
                renamer.renameVariablesAndSkolemConstants();
        Term[] result = new Term[renamedGoalFormulas.length];
        for (int i = 0; i < renamedGoalFormulas.length; i++) {
            result[i] =
                    TB.applyElementary(services, c.pre.heap, renamedGoalFormulas[i]);
        }
        return result;
    }


    private static Term[] buildFormulasFromGoals(ImmutableList<Goal> symbExecGoals) {
        Term[] result = new Term[symbExecGoals.size()];
        int i = 0;
        for (final Goal symbExecGoal : symbExecGoals) {
            result[i] = buildFormulaFromGoal(symbExecGoal);
            i++;
        }
        return result;
    }


    private static Term buildFormulaFromGoal(Goal symbExecGoal) {
        Term result = TB.tt();
        for (final SequentFormula f : symbExecGoal.sequent().antecedent()) {
            result = TB.and(result, f.formula());
        }
        for (final SequentFormula f : symbExecGoal.sequent().succedent()) {
            result = TB.and(result, TB.not(f.formula()));
        }
        return result;
    }


    protected static void addContractApplicationTaclets(Goal initiatingGoal,
                                                        Proof symbExecProof) {
        final ImmutableList<Goal> openGoals = symbExecProof.openGoals();
        for (final Goal openGoal : openGoals) {
            final ImmutableSet<NoPosTacletApp> ruleApps =
                    openGoal.indexOfTaclets().allNoPosTacletApps();
            for (final NoPosTacletApp ruleApp : ruleApps) {
                final Taclet t = ruleApp.taclet();
                if (t.getSurviveSymbExec()) {
                    initiatingGoal.addTaclet(t, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
                }
            }
        }
    }
}