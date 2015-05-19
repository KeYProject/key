/**
 * 
 */
package de.uka.ilkd.key.proof.io.intermediate;

import org.key_project.util.collection.ImmutableList;

import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.util.Pair;

/**
 * 
 * TODO: Document.
 *
 * @author Dominic Scheurer
 */
public class BuiltInAppIntermediate implements AppIntermediate {

    private String ruleName = null;
    private Pair<Integer, PosInTerm> posInfo = null;
    private String contract = null;
    private ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts = null;
    private String[] newNames = null;

    public BuiltInAppIntermediate(String ruleName,
            Pair<Integer, PosInTerm> pos, String contract,
            ImmutableList<Pair<Integer, PosInTerm>> builtInIfInsts,
            String[] newNames) {
        this.ruleName = ruleName;
        this.posInfo = pos;
        this.contract = contract;
        this.builtInIfInsts = builtInIfInsts;
        this.newNames = newNames;
    }

    public String[] getNewNames() {
        return newNames;
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

}
