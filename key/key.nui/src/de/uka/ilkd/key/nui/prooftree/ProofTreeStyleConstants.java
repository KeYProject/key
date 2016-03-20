package de.uka.ilkd.key.nui.prooftree;

/**
 * Constants used for defining names and paths for the decoration of the proof
 * tree (icon paths, CSS classes etc.).
 * 
 * @author Matthias Schultheis
 * @author Patrick Jattke
 * @version 1.0
 */
public final class ProofTreeStyleConstants {

    /** CSS filename for the proof tree. */
    public static final String CSS_FILE = "treeView.css";

    /* Name of CSS classes - see file treeView.css at resources folder */

    /** CSS class for a branch. */
    public static final String CSS_PROOF_TREE = "proof_tree";

    /** CSS class for a branch. */
    public static final String CSS_NODE_BRANCH = "branch_node";

    /** CSS class for a closed node. */
    public static final String CSS_NODE_CLOSED = "closed_node";

    /** CSS class for an open node. */
    public static final String CSS_NODE_OPEN = "open_node";

    /** CSS class for a leaf node. */
    public static final String CSS_NODE_LEAF = "leaf_node";

    /** CSS class for a linked node. */
    public static final String CSS_NODE_LINKED = "linked_node";

    /** CSS class for an interactive node. */
    public static final String CSS_NODE_INTERACTIVE = "interactive_node";

    /** CSS class for a node that has notes. */
    public static final String CSS_NODE_NOTES = "notes_node";

    /** CSS class for an active node. */
    public static final String CSS_NODE_ACTIVE = "active_node";

    /** CSS class for an highlighted node. */
    public static final String CSS_NODE_HIGHLIGHT = "highlighted_node";

    /**
     * The private constructor is not called as it is only a utility class.
     */
    private ProofTreeStyleConstants() {
    }
}
