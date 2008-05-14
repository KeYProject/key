package de.uka.ilkd.key.visualdebugger.executiontree;

import java.util.LinkedList;

/**
 * The Class ETPath.
 * 
 * Instances of this class describe a path in a execution tree from a certain
 * node to a certain node using a LinkedList. If only a target node is given the
 * path will start from the root.
 */
public class ETPath {

    /** The node from where the path starts. */
    private ETNode fromNode = null;

    /** The node where the path ends. */
    private ETNode toNode = null;

    /** A temporary variable. */
    private ETNode currentNode = null;

    /** The path. */
    private LinkedList path = new LinkedList();

    /**
     * Instantiates a new ETPath.
     * 
     * @param from
     *                the start
     * @param to
     *                the end
     */
    public ETPath(ETNode from, ETNode to) {

        fromNode = from;
        toNode = to;
        buildPath();

    }

    /**
     * Builds the path.
     */
    public void buildPath() {

        currentNode = toNode;

        if (!(toNode.equals(fromNode))) {

            while (!(currentNode.equals(fromNode))) {

                path.add(currentNode);
                currentNode = currentNode.getParent();
            }
        } else {
            System.out.println("End = Start.");
        }

    }

    /**
     * Gets the path.
     * 
     * @return the path
     */
    public LinkedList getPath() {
        return path;
    }

    /**
     * Contains.
     * 
     * Contains returns true, if a given ETNode is part of the path.
     * 
     * @param etn
     *                the ETNode
     * @return true, if successful
     */
    public boolean contains(ETNode etn) {

        return path.contains(etn);

    }

}
