/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.proof;

import java.io.PrintWriter;

import de.uka.ilkd.key.informationflow.po.InfFlowProofSymbols;
import de.uka.ilkd.key.logic.JTerm;
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
    private SideProofStatistics sideProofStatistics = null;

    public InfFlowProof(String name, Sequent sequent, String header, TacletIndex rules,
            BuiltInRuleIndex builtInRules, InitConfig initConfig) {
        super(name, sequent, header, rules, builtInRules, initConfig);
    }

    public InfFlowProof(String name, JTerm problem, String header, InitConfig initConfig) {
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
        assert infFlowSymbols != null;
        return infFlowSymbols;
    }

    public void addIFSymbol(Object s) {
        assert s != null;
        if (s instanceof JTerm) {
            infFlowSymbols.add((JTerm) s);
        } else if (s instanceof Named) {
            infFlowSymbols.add((Named) s);
        } else {
            throw new UnsupportedOperationException("Not a valid proof symbol for IF proofs.");
        }
    }

    public void addLabeledIFSymbol(Object s) {
        assert s != null;
        if (s instanceof JTerm) {
            infFlowSymbols.addLabeled((JTerm) s);
        } else if (s instanceof Named) {
            infFlowSymbols.addLabeled((Named) s);
        } else {
            throw new UnsupportedOperationException("Not a valid proof symbol for IF proofs.");
        }
    }

    public void addTotalTerm(JTerm p) {
        assert p != null;
        infFlowSymbols.addTotalTerm(p);
    }

    public void addLabeledTotalTerm(JTerm p) {
        assert p != null;
        infFlowSymbols.addLabeledTotalTerm(p);
    }

    public void addGoalTemplates(Taclet t) {
        assert t != null;
        ImmutableList<TacletGoalTemplate> temps = t.goalTemplates();
        assert temps != null;
        for (TacletGoalTemplate tgt : temps) {
            for (SequentFormula sf : tgt.sequent().antecedent()
                    .asList()) {
                addLabeledTotalTerm((JTerm) sf.formula());
            }
            for (SequentFormula sf : tgt.sequent().succedent().asList()) {
                addLabeledTotalTerm((JTerm) sf.formula());
            }
        }
    }

    public void unionIFSymbols(InfFlowProofSymbols symbols) {
        assert symbols != null;
        infFlowSymbols = infFlowSymbols.union(symbols);
    }

    public void unionLabeledIFSymbols(InfFlowProofSymbols symbols) {
        assert symbols != null;
        infFlowSymbols = infFlowSymbols.unionLabeled(symbols);
    }

    public String printIFSymbols() {
        return infFlowSymbols.printProofSymbols();
    }

    public boolean hasSideProofs() {
        return this.sideProofStatistics != null;
    }

    public void addSideProof(InfFlowProof proof) {
        assert proof != null;
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
        assert stat != null;
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

    @Override
    public void printSymbols(PrintWriter ps) {
        // we just believe that we are in an Infomration Flow proof-obligation.
        // po instanceof AbstractInfFlowPO && (po instanceof InfFlowCompositePO
        if (!getIFSymbols().isFreshContract())
            ps.print(printIFSymbols());
    }
}
