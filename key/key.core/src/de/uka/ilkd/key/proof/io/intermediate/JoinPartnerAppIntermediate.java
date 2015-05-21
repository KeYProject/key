/**
 * 
 */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

/**
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class JoinPartnerAppIntermediate extends BuiltInAppIntermediate {

    private int joinNodeId = 0;

    /**
     * TODO: Document.
     *
     * @param ruleName
     * @param pos
     * @param contract
     * @param builtInIfInsts
     * @param newNames
     */
    public JoinPartnerAppIntermediate(String ruleName,
            Pair<Integer, PosInTerm> pos, String contract,
            ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts,
            int joinNodeId, ImmutableList<Name> newNames) {
        super(ruleName, pos, contract, builtInIfInsts, newNames);
        this.joinNodeId = joinNodeId;
    }

    /**
     * @return the joinNodeId
     */
    public int getJoinNodeId() {
        return joinNodeId;
    }

}
