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
 *
 */
public class JoinAppIntermediate extends BuiltInAppIntermediate {

    private int id = 0;
    private String joinProc = null;
    private int nrPartners = 0;

    /**
     * TODO: Document.
     *
     * @param ruleName
     * @param pos
     * @param contract
     * @param builtInIfInsts
     * @param newNames
     */
    public JoinAppIntermediate(String ruleName, Pair<Integer, PosInTerm> pos,
            String contract,
            ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts, int id,
            String joinProc, int nrPartners, ImmutableList<Name> newNames) {
        super(ruleName, pos, contract, builtInIfInsts, newNames);
        this.id = id;
        this.joinProc = joinProc;
        this.nrPartners = nrPartners;
    }

    /**
     * @return the id
     */
    public int getId() {
        return id;
    }

    /**
     * @return the joinProc
     */
    public String getJoinProc() {
        return joinProc;
    }

    /**
     * @return the nrPartners
     */
    public int getNrPartners() {
        return nrPartners;
    }

}
