/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.proof;

import de.uka.ilkd.key.informationflow.po.InfFlowProofSymbols;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.Statistics;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.rule.Taclet;

import org.key_project.logic.Named;
import org.key_project.prover.rules.tacletbuilder.TacletGoalTemplate;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * The proof object used by Information Flow Proofs.
 *
 * It manages some additional data specific to their kind. The concept of side proofs is actually
 * more general than just to be useful for Information Flow proofs, but as only they are using the
 * feature, it is currently moved into this subclass.
 */
public class InfFlowProof extends Proof {

    /**
     * For saving and loading Information-Flow proofs, we need to remember the according taclets,
     * program variables, functions and such.
     */
    private InfFlowProofSymbols infFlowSymbols = new InfFlowProofSymbols();
    /**
     * Aggregated proof statistics from other proofs which contributed to this one.
     */
    private @Nullable SideProofStatistics sideProofStatistics = null;

    public InfFlowProof(String name, Sequent sequent, String header, TacletIndex rules,
            BuiltInRuleIndex builtInRules, InitConfig initConfig) {
        super(name, sequent, header, rules, builtInRules, initConfig);
    }

    public InfFlowProof(String name, Term problem, String header, InitConfig initConfig) {
        super(name, problem, header, initConfig);
    }

    public InfFlowProof(String name, InitConfig initConfig) {
        super(name, initConfig);
    }

    public InfFlowProofSymbols removeInfFlowProofSymbols() {
        InfFlowProofSymbols symbols = infFlowSymbols;
        infFlowSymbols = new InfFlowProofSymbols();
        return symbols;
    }

    public InfFlowProofSymbols getIFSymbols() {
        return infFlowSymbols;
    }

    public void addIFSymbol(Object s) {
        if (s instanceof Term) {
            infFlowSymbols.add((Term) s);
        } else if (s instanceof Named) {
            infFlowSymbols.add((Named) s);
        } else {
            throw new UnsupportedOperationException("Not a valid proof symbol for IF proofs.");
        }
    }

    public void addLabeledIFSymbol(Object s) {
        if (s instanceof Term) {
            infFlowSymbols.addLabeled((Term) s);
        } else if (s instanceof Named) {
            infFlowSymbols.addLabeled((Named) s);
        } else {
            throw new UnsupportedOperationException("Not a valid proof symbol for IF proofs.");
        }
    }

    public void addTotalTerm(Term p) {
        infFlowSymbols.addTotalTerm(p);
    }

    public void addLabeledTotalTerm(Term p) {
        infFlowSymbols.addLabeledTotalTerm(p);
    }

    public void addGoalTemplates(Taclet t) {
        ImmutableList<TacletGoalTemplate> temps = t.goalTemplates();
        for (TacletGoalTemplate tgt : temps) {
            for (SequentFormula sf : tgt.sequent().antecedent()
                    .asList()) {
                addLabeledTotalTerm((Term) sf.formula());
            }
            for (SequentFormula sf : tgt.sequent().succedent().asList()) {
                addLabeledTotalTerm((Term) sf.formula());
            }
        }
    }

    public void unionIFSymbols(InfFlowProofSymbols symbols) {
        infFlowSymbols = infFlowSymbols.union(symbols);
    }

    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols) {
        infFlowSymbols = infFlowSymbols.unionLabeled(symbols);
    }

    public String printIFSymbols() {
        return infFlowSymbols.printProofSymbols();
    }

    public boolean hasSideProofs() {
        return this.sideProofStatistics != null;
    }

    public void addSideProof(InfFlowProof proof) {
        if (proof.hasSideProofs()) {
            if (this.hasSideProofs()) {
                sideProofStatistics = sideProofStatistics.add(proof.sideProofStatistics);
            } else {
                sideProofStatistics = SideProofStatistics.create(proof.sideProofStatistics);
            }
            proof.sideProofStatistics = null;
        }
        addSideProofStatistics(proof.getStatistics());
    }

    private void addSideProofStatistics(Statistics stat) {
        if (this.hasSideProofs()) {
            sideProofStatistics = sideProofStatistics.add(stat);
        } else {
            sideProofStatistics = SideProofStatistics.create(stat);
        }
    }

    /**
     * returns statistics of possible side proofs that contributed to this proof
     *
     * @return the proof statistics
     */
    public SideProofStatistics getSideProofStatistics() {
        return sideProofStatistics;
    }

}
