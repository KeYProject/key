package de.uka.ilkd.key.proof.io.intermediate;

import de.uka.ilkd.key.proof.io.intermediate.NodeIntermediate;

public abstract class NodeIntermediateWalker {
    /** the root the walker starts */
    private NodeIntermediate root;

    /** the current visited level */
    private int depth = -1;

    /** create the Walker 
     * @param root the NodeIntermediate where to begin
     */
    public NodeIntermediateWalker(NodeIntermediate root) {
        this.root = root;
    }

    /** returns start point of the walker
     * @return root of the AST to walk through
     */
    public NodeIntermediate root() {
        return root;
    }

    /** starts the walker*/
    public void start() {
        walk(root);
    }

    /** 
     * returns the current vistted level
     */
    public int depth() {
        return depth;
    }

    /** walks through the AST. While keeping track of the current node
     * @param node the JavaProgramElement the walker is at 
     */
    protected void walk(NodeIntermediate node) {
        doAction(node);
        
        for (NodeIntermediate child : node.getChildren()) {
            walk(child);
        }
    }

    /** the action that is performed just before leaving the node the
     * last time 
     */
    protected abstract void doAction(NodeIntermediate node);
}
