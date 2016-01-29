package de.uka.ilkd.key.nui.prooftree;

import java.util.LinkedList;
import java.util.List;

/**
 * Represents an inner node. Is used to create a graphical representation of
 * a proof tree consisting of {@link de.uka.ilkd.key.proof.Node} objects.
 * 
 * @author Matthias Schultheis
 * @author Patrick Jattke
 *
 */
public class NUIInnerNode extends NUINode {
    
    @Override
    public List<NUINode> search(final String term){
        List<NUINode> l = new LinkedList<>();
        if(getLabel().toLowerCase().contains(term.toLowerCase())){
                    l.add(this);
        }
        return l;
    }

    /**
     * The related proof node of the inner node.
     */
    private final de.uka.ilkd.key.proof.Node proofNode;

    /**
     * Creates a new inner node. 
     * 
     * @param pNode
     * 			The related proof node of the inner node.
     */
    public NUIInnerNode(final de.uka.ilkd.key.proof.Node pNode) {
    	super();
        this.proofNode = pNode;
    }

    /**
     * Returns the proof node of the inner node.
     * 
     * @return proofNode
     * 			The proof node of the inner node.
     */
    public final de.uka.ilkd.key.proof.Node getProofNode() {
        return proofNode;
    }
}
