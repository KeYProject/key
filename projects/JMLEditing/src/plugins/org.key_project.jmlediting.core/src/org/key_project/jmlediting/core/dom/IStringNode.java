package org.key_project.jmlediting.core.dom;

/**
 * This nodes defines a special {@link IASTNode} just containing a string and no
 * children.
 *
 * @author Moritz Lichter
 *
 */
public interface IStringNode extends IASTNode {

   /**
    * The string value of this node.
    *
    * @return the string
    */
   String getString();

}
