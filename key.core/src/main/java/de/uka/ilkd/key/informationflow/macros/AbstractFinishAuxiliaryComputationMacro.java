/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.macros;

import java.util.Map;
import java.util.Set;

import de.uka.ilkd.key.informationflow.po.IFProofObligationVars;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.macros.AbstractProofMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.InfFlowProgVarRenamer;

import org.key_project.util.collection.ImmutableList;


/**
 *
 * @author christoph
 */
public abstract class AbstractFinishAuxiliaryComputationMacro extends AbstractProofMacro {

    @Override
    public String getName() {
        return "Finish auxiliary computation";
    }

    @Override
    public String getCategory() {
        return "Auxiliary Computation";
    }

    @Override
    public String getDescription() {
        return "Finish auxiliary computation.";
    }

    static Term calculateResultingTerm(Proof proof, IFProofObligationVars ifVars, Goal initGoal) {
        final Term[] goalFormulas1 =
            buildExecution(ifVars.c1, ifVars.getMapFor(ifVars.c1), proof.openGoals(), initGoal);
        final Term[] goalFormulas2 =
            buildExecution(ifVars.c2, ifVars.getMapFor(ifVars.c2), proof.openGoals(), initGoal);
        final TermBuilder tb = proof.getServices().getTermBuilder();
        Term composedStates = tb.ff();
        for (int i = 0; i < goalFormulas1.length; i++) {
            for (int j = i; j < goalFormulas2.length; j++) {
                final Term composedState = tb.and(goalFormulas1[i], goalFormulas2[j]);
                composedStates = tb.or(composedStates, composedState);
            }
        }
        return composedStates;
    }

    /**
     * Merge namespaces.
     *
     * @param initiatingProof the initiating proof
     * @param sideProof the side proof
     */
    protected final void mergeNamespaces(Proof initiatingProof, Proof sideProof) {
        NamespaceSet initiatingProofNS = initiatingProof.getServices().getNamespaces();
        NamespaceSet sideProofNS = sideProof.getServices().getNamespaces();

        mergeNamespace(initiatingProofNS.variables(), sideProofNS.variables());
        mergeNamespace(initiatingProofNS.programVariables(), sideProofNS.programVariables());
        mergeNamespace(initiatingProofNS.functions(), sideProofNS.functions());
        mergeNamespace(initiatingProofNS.ruleSets(), sideProofNS.ruleSets());
        mergeNamespace(initiatingProofNS.sorts(), sideProofNS.sorts());
        mergeNamespace(initiatingProofNS.choices(), sideProofNS.choices());
    }

    private final <E extends Named> void mergeNamespace(Namespace<E> tar, Namespace<E> src) {
        for (E el : src.allElements()) {
            if (!tar.contains(el)) {
                tar.add(el);
            }
        }
    }

    private static Term[] buildExecution(ProofObligationVars c, Map<Term, Term> vsMap,
            ImmutableList<Goal> symbExecGoals, Goal initGoal) {
        Services services = initGoal.proof().getServices();
        final Term[] goalFormulas = buildFormulasFromGoals(symbExecGoals);
        final InfFlowProgVarRenamer renamer = new InfFlowProgVarRenamer(goalFormulas, vsMap,
            c.postfix, initGoal, services.getOverlay(initGoal.getLocalNamespaces()));
        final Term[] renamedGoalFormulas = renamer.renameVariablesAndSkolemConstants();
        Term[] result = new Term[renamedGoalFormulas.length];
        final TermBuilder tb = services.getTermBuilder();
        for (int i = 0; i < renamedGoalFormulas.length; i++) {
            result[i] = tb.applyElementary(c.pre.heap, renamedGoalFormulas[i]);
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
        final TermBuilder tb = symbExecGoal.proof().getServices().getTermBuilder();
        final TermFactory tf = symbExecGoal.proof().getServices().getTermFactory();
        Term result = tb.tt();
        for (final SequentFormula f : symbExecGoal.sequent().antecedent()) {
            result = tb.and(result, f.formula());
        }
        for (final SequentFormula f : symbExecGoal.sequent().succedent()) {
            result = tb.and(result, tb.not(f.formula()));
        }
        result = TermLabel.removeIrrelevantLabels(result, tf);
        return result;
    }

    protected static void addContractApplicationTaclets(Goal initiatingGoal, Proof symbExecProof) {
        final ImmutableList<Goal> openGoals = symbExecProof.openGoals();
        for (final Goal openGoal : openGoals) {
            final Set<NoPosTacletApp> ruleApps = openGoal.indexOfTaclets().allNoPosTacletApps();
            for (final NoPosTacletApp ruleApp : ruleApps) {
                final Taclet t = ruleApp.taclet();
                if (t.getSurviveSymbExec()) {
                    initiatingGoal.addTaclet(t, SVInstantiations.EMPTY_SVINSTANTIATIONS, true);
                }
            }
        }
    }
}
