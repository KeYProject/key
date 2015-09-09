package org.key_project.jmlediting.ui.outlineView;

import java.util.List;

import org.eclipse.jdt.core.dom.Comment;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;
import org.key_project.jmlediting.core.dom.INodeTraverser;

/**
 * Contains {@link IASTNode} with a Read able string that should be shown in the Outline.
 * 
 * @author Timm Lippert
 *
 */

public class JMLComments implements IASTNode {

   Comment node;
   String text;
   String type;
   
   /**
    * 
    * @param commenttext </br>The Text That should be shown in the Outline.
    * @param node </br>The Comments {@link IASTNode}.
    * @param type </br>type of the Comment for example type.
    */
   
   public JMLComments(String commenttext,Comment node,String type) {
      text= commenttext;
      this.node = node;
      this.type = type;
   }
   @Override
   public String toString() {
      return text;
   }
   @Override
   public int getStartOffset() {
      return node.getStartPosition();
   }
   @Override
   public int getEndOffset() {
      return node.getLength()+node.getStartPosition();
   }
   @Override
   public boolean containsOffset(int offset) {
      return false;
   }
   @Override
   public boolean containsCaret(int caretPosition) {
      return false;
   }
   @Override
   public int getType() {
      return 0;
   }
   @Override
   public List<IASTNode> getChildren() {
      return null;
   }
   @Override
   public <T> T search(INodeSearcher<T> searcher) {
      return null;
   }
   @Override
   public <T> T traverse(INodeTraverser<T> traverser, T init) {
      return null;
   }
   @Override
   public String prettyPrintAST() {
      return text;
   }
   
}
