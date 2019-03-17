/**
 * 
 */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

/**
 * Encapsulates intermediate information for constructing a built-in rule application.
 *
 * @author Dominic Scheurer
 */
public class BuiltInAppIntermediate extends AppIntermediate {

    private String ruleName = null;
    private Pair<Integer, PosInTerm> posInfo = null;
    private String contract = null;
    private ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts = null;
    private ImmutableList<Name> newNames = null;

    public BuiltInAppIntermediate(String ruleName,
            Pair<Integer, PosInTerm> pos, String contract,
            ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts,
            ImmutableList<Name> newNames) {
        this.ruleName = ruleName;
        this.posInfo = pos;
        this.contract = contract;
        this.builtInIfInsts = builtInIfInsts;
        this.newNames = newNames;
    }

    public String getRuleName() {
        return ruleName;
    }

    public Pair<Integer, PosInTerm> getPosInfo() {
        return posInfo;
    }

    public String getContract() {
        return contract;
    }

    public ImmutableList<Pair<Integer, PosInTerm>> getBuiltInIfInsts() {
        return builtInIfInsts;
    }

    /* (non-Javadoc)
     * @see de.uka.ilkd.key.proof.io.intermediate.AppIntermediate#getNewNames()
     */
    @Override
    public ImmutableList<Name> getNewNames() {
        return newNames;
    }

}
