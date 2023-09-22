/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.merge;

import java.util.Set;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.util.mergerule.SymbolicExecutionState;

import org.key_project.util.collection.ImmutableList;

/**
 * Rule application class for close-after-merge rule applications.
 *
 * @author Dominic Scheurer
 */
public class CloseAfterMergeRuleBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private Node partnerNode, correspondingMergeNode;
    private SymbolicExecutionState mergeNodeState;
    private SymbolicExecutionState partnerState;
    private Term pc;
    private Set<Name> newNames;

    public CloseAfterMergeRuleBuiltInRuleApp(BuiltInRule builtInRule, PosInOccurrence pio,
            Node thePartnerNode, Node correspondingMergeNode, SymbolicExecutionState mergeNodeState,
            SymbolicExecutionState partnerState, Term pc, Set<Name> newNames) {
        this(builtInRule, pio);
        setThePartnerNode(thePartnerNode);
        setCorrespondingMergeNode(correspondingMergeNode);
        setMergeNodeState(mergeNodeState);
        setPartnerState(partnerState);
        setPc(pc);
        setNewNames(newNames);
    }

    public CloseAfterMergeRuleBuiltInRuleApp(BuiltInRule builtInRule, PosInOccurrence pio) {
        super(builtInRule, pio);
    }

    @Override
    public AbstractBuiltInRuleApp replacePos(PosInOccurrence newPos) {
        return null;
    }

    @Override
    public IBuiltInRuleApp setIfInsts(ImmutableList<PosInOccurrence> ifInsts) {
        setMutable(ifInsts);
        return this;
    }

    @Override
    public AbstractBuiltInRuleApp tryToInstantiate(Goal goal) {
        return this;
    }

    @Override
    public boolean complete() {
        return partnerNode != null && correspondingMergeNode != null && mergeNodeState != null
                && partnerState != null && pc != null;
    }

    // // GETTERS AND SETTERS // //

    public Node getThePartnerNode() {
        return partnerNode;
    }

    public void setThePartnerNode(Node thePartnerNode) {
        this.partnerNode = thePartnerNode;
    }

    public Node getCorrespondingMergeNode() {
        return correspondingMergeNode;
    }

    public void setCorrespondingMergeNode(Node correspondingMergeNode) {
        this.correspondingMergeNode = correspondingMergeNode;
    }

    public SymbolicExecutionState getMergeState() {
        return mergeNodeState;
    }

    public void setMergeNodeState(SymbolicExecutionState mergeState) {
        this.mergeNodeState = mergeState;
    }

    public SymbolicExecutionState getPartnerSEState() {
        return partnerState;
    }

    public void setPartnerState(SymbolicExecutionState thisSEState) {
        this.partnerState = thisSEState;
    }

    public Term getPc() {
        return pc;
    }

    public void setPc(Term pc) {
        this.pc = pc;
    }

    public Set<Name> getNewNames() {
        return newNames;
    }

    public void setNewNames(Set<Name> newNames) {
        this.newNames = newNames;
    }

}
