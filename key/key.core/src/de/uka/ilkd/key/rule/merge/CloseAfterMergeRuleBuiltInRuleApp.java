package de.uka.ilkd.key.rule.merge;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import mergerule.SymbolicExecutionState;

/**
 * Rule application class for close-after-merge rule applications.
 * 
 * @author Dominic Scheurer
 */
public class CloseAfterMergeRuleBuiltInRuleApp extends AbstractBuiltInRuleApp {

    private Node partnerNode, correspondingMergeNode;

    private SymbolicExecutionState mergeNodeState = null;
    private SymbolicExecutionState partnerState = null;
    private Term pc = null;

    public CloseAfterMergeRuleBuiltInRuleApp(BuiltInRule builtInRule,
            PosInOccurrence pio, Node thePartnerNode,
            Node correspondingMergeNode, SymbolicExecutionState mergeNodeState,
            SymbolicExecutionState partnerState, Term pc) {
        this(builtInRule, pio);
        setThePartnerNode(thePartnerNode);
        setCorrespondingMergeNode(correspondingMergeNode);
        setMergeNodeState(mergeNodeState);
        setPartnerState(partnerState);
        setPc(pc);
    }

    public CloseAfterMergeRuleBuiltInRuleApp(BuiltInRule builtInRule,
            PosInOccurrence pio) {
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
        return partnerNode != null && correspondingMergeNode != null
                && mergeNodeState != null && partnerState != null && pc != null;
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

}
