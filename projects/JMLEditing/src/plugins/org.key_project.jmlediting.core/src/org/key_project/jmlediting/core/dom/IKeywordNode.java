package org.key_project.jmlediting.core.dom;

import org.key_project.jmlediting.core.profile.syntax.IKeyword;

/**
 * Defines a special IASTNode for the occurrence of an {@link IKeyword} in the
 * AST. This node does not have children.
 * 
 * @author Moritz Lichter
 *
 */
public interface IKeywordNode extends IASTNode {

   /**
    * Returns the {@link IKeyword} of which an instance was found.
    * 
    * @return the found keyword
    */
   IKeyword getKeyword();

   /**
    * Returns the actual keyword found. The returned string is an element of
    * {@code this.getKeyword().getKeywords()}.
    * 
    * @return the actual string found
    */
   String getKeywordInstance();

}
