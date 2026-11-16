/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.join;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Node;

import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Represents the partners of a join operation.
 *
 * @author Benjamin Niedermann
 */
@NullMarked
public class ProspectivePartner {
    private final JTerm[] updates = new JTerm[2];
    private final JTerm commonFormula;
    private final SequentFormula[] formula =
        new SequentFormula[2];
    private final Node[] nodes = new Node[2];
    private @Nullable JTerm commonPredicate = null;
    private @Nullable Node commonParent = null;
    private @Nullable SequentFormula formulaForHiding = null;

    /**
     * Constructs a new prospective partner object, i.e. a structure comprising the information
     * about two partners of a join operation.
     *
     * @param commonFormula The common formula of a join operation, i.e. the "symbolic state -
     *        program counter" part of the join.
     * @param node1 The first node of the join.
     * @param formula1 The first join formula.
     * @param update1 The first symbolic state.
     * @param node2 The second node of the join.
     * @param formula2 The second join formula.
     * @param update2 The second symbolic state.
     */
    public ProspectivePartner(JTerm commonFormula, Node node1,
            SequentFormula formula1, JTerm update1,
            Node node2, SequentFormula formula2, JTerm update2) {
        super();
        this.commonFormula = commonFormula;
        formula[0] = formula1;
        formula[1] = formula2;
        updates[0] = update1;
        updates[1] = update2;
        nodes[0] = node1;
        nodes[1] = node2;
    }

    public JTerm getCommonFormula() {
        return commonFormula;
    }

    public Node getNode(int index) {
        return nodes[index];
    }

    public JTerm getUpdate(int index) {
        return updates[index];
    }

    public void setCommonPredicate(JTerm commonPredicate) {
        this.commonPredicate = commonPredicate;
    }

    public @Nullable JTerm getCommonPredicate() {
        return commonPredicate;
    }

    /**
     * Sets the common parent node of this prospective join partner pair and derives the hide
     * formula from its applied rule application if present.
     * <p>
     * A parent node's applied rule application carries a position whenever the pair's formula for
     * hiding is derivable; the dereferences of the (nullable) applied rule app and its (nullable)
     * position are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public void setCommonParent(Node commonParent) {
        this.commonParent = commonParent;
        if (commonParent.getAppliedRuleApp() != null
                && commonParent.getAppliedRuleApp().posInOccurrence() != null) {
            setFormulaForHiding(
                commonParent.getAppliedRuleApp().posInOccurrence()
                        .sequentFormula());
        }
    }

    private void setFormulaForHiding(
            SequentFormula formulaForHiding) {
        this.formulaForHiding = formulaForHiding;
    }

    public @Nullable SequentFormula getFormulaForHiding() {
        return formulaForHiding;
    }

    public @Nullable Node getCommonParent() {
        return commonParent;
    }

    public Sequent getSequent(int index) {
        return getNode(index).sequent();
    }

    public SequentFormula getFormula(int i) {
        return formula[i];
    }

}
