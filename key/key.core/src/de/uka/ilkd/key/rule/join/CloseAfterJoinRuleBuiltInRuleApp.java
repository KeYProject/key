package de.uka.ilkd.key.rule.join;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.AbstractBuiltInRuleApp;
import de.uka.ilkd.key.rule.BuiltInRule;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;

/**
 * Rule application class for close-after-join rule applications.
 * 
 * @author Dominic Scheurer
 */
public class CloseAfterJoinRuleBuiltInRuleApp extends AbstractBuiltInRuleApp {

	private Node thePartnerNode, correspondingJoinNode;
	
	public CloseAfterJoinRuleBuiltInRuleApp(
			BuiltInRule builtInRule,
			PosInOccurrence pio,
			Node thePartnerNode,
			Node correspondingJoinNode) {
        this(builtInRule, pio);
        this.setThePartnerNode(thePartnerNode);
        this.setCorrespondingJoinNode(correspondingJoinNode);
    }
	
	public CloseAfterJoinRuleBuiltInRuleApp(BuiltInRule builtInRule, PosInOccurrence pio) {
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
        return true;
    }

	public Node getThePartnerNode() {
		return thePartnerNode;
	}

	public void setThePartnerNode(Node thePartnerNode) {
		this.thePartnerNode = thePartnerNode;
	}

	public Node getCorrespondingJoinNode() {
		return correspondingJoinNode;
	}

	public void setCorrespondingJoinNode(Node correspondingJoinNode) {
		this.correspondingJoinNode = correspondingJoinNode;
	}

}
