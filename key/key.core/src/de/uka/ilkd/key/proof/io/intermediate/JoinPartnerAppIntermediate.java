/**
 * 
 */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

/**
 * Encapsulates intermediate information for constructing a close-join-partner rule application.
 *
 * @author Dominic Scheurer
 */
public class JoinPartnerAppIntermediate extends BuiltInAppIntermediate {

    private int joinNodeId = 0;
    
    /**
     * Constructs a new close-join-partner intermediate application.
     *
     * @param ruleName The name of the rule; should be "CloseAfterJoin".
     * @param pos Position information for the join rule application (Symbolic State - Program Counter formula).
     * @param joinNodeId The ID of the corresponding join node.
     * @param newNames New names registered in the course of partner goal closing.
     */
    public JoinPartnerAppIntermediate(String ruleName,
            Pair<Integer, PosInTerm> pos,
            int joinNodeId, ImmutableList<Name> newNames) {
        super(ruleName, pos, null, null, newNames);
        
        assert ruleName.equals("CloseAfterJoin") :
            "Check if something should be changed when implementing a new rule for join partners.";
        
        this.joinNodeId = joinNodeId;
    }

    /**
     * @return The ID of the corresponding join node.
     */
    public int getJoinNodeId() {
        return joinNodeId;
    }

}
