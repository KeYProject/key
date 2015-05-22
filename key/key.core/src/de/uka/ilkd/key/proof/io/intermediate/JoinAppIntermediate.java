/**
 * 
 */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

/**
 * Encapsulates intermediate information for constructing a join rule application.
 *
 * @author Dominic Scheurer
 */
public class JoinAppIntermediate extends BuiltInAppIntermediate {

    private int id = 0;
    private String joinProc = null;
    private int nrPartners = 0;
    
    /**
     * Constructs a new join rule.
     *
     * @param ruleName Name of the rule; should be "JoinRule".
     * @param pos Position information for the join rule application (Symbolic State - Program Counter formula).
     * @param id ID of the join rule application (should have been stored during proof saving and should
     *   match the joinNodeId fields of the corresponding partner nodes).
     * @param joinProc The name of the join procedure used during joining.
     * @param nrPartners Number of involved join partners.
     * @param newNames New names registered in the course of the join rule application.
     */
    public JoinAppIntermediate(String ruleName, Pair<Integer, PosInTerm> pos, int id,
            String joinProc, int nrPartners, ImmutableList<Name> newNames) {
        super(ruleName, pos, null, null, newNames);
        
        assert ruleName.equals("JoinRule") : "This was somehow unexpected; are there other join rules than JoinRule?";
        
        this.id = id;
        this.joinProc = joinProc;
        this.nrPartners = nrPartners;
    }

    /**
     * @return ID of the join rule application (should have been stored during proof saving and should
     *   match the joinNodeId fields of the corresponding partner nodes).
     */
    public int getId() {
        return id;
    }

    /**
     * @return The name of the join procedure used during joining.
     */
    public String getJoinProc() {
        return joinProc;
    }

    /**
     * @return Number of involved join partners.
     */
    public int getNrPartners() {
        return nrPartners;
    }

}
