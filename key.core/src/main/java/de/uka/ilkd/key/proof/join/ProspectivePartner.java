// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.join;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

/**
 * Represents the partners of a join operation.
 *
 * @author Benjamin Niedermann
 */
public class ProspectivePartner {
    private final Term[] updates = new Term[2];
    private final Term commonFormula;
    private final SequentFormula[] formula = new SequentFormula[2];
    private final Node[] nodes = new Node[2];
    private Term commonPredicate = null;
    private Node commonParent = null;
    private SequentFormula formulaForHiding = null;

    /**
     * Constructs a new prospective partner object, i.e. a
     * structure comprising the information about two partners
     * of a join operation.
     *
     * @param commonFormula The common formula of a join operation,
     *   i.e. the "symbolic state - program counter" part of the join.
     * @param node1 The first node of the join.
     * @param formula1 The first join formula.
     * @param update1 The first symbolic state.
     * @param node2 The second node of the join.
     * @param formula2 The second join formula.
     * @param update2 The second symbolic state.
     */
    public ProspectivePartner(Term commonFormula, Node node1,
            SequentFormula formula1, Term update1, Node node2,
            SequentFormula formula2, Term update2) {
        super();
        this.commonFormula = commonFormula;
        formula[0] = formula1;
        formula[1] = formula2;
        updates[0] = update1;
        updates[1] = update2;
        nodes[0] = node1;
        nodes[1] = node2;
    }

    public Term getCommonFormula() {
        return commonFormula;
    }

    public Node getNode(int index) {
        return nodes[index];
    }

    public Term getUpdate(int index) {
        return updates[index];
    }

    public void setCommonPredicate(Term commonPredicate) {
        this.commonPredicate = commonPredicate;
    }

    public Term getCommonPredicate() {
        return commonPredicate;
    }

    public void setCommonParent(Node commonParent) {
        this.commonParent = commonParent;
        if (commonParent.getAppliedRuleApp() != null
                && commonParent.getAppliedRuleApp().posInOccurrence() != null) {
            setFormulaForHiding(commonParent.getAppliedRuleApp()
                    .posInOccurrence().sequentFormula());
        }
    }

    private void setFormulaForHiding(SequentFormula formulaForHiding) {
        this.formulaForHiding = formulaForHiding;
    }

    public SequentFormula getFormulaForHiding() {
        return formulaForHiding;
    }

    public Node getCommonParent() {
        return commonParent;
    }

    public Sequent getSequent(int index) {
        return getNode(index).sequent();
    }

    public SequentFormula getFormula(int i) {
        return formula[i];
    }

}