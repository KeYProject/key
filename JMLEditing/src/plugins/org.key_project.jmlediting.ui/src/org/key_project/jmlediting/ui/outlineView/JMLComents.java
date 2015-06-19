package org.key_project.jmlediting.ui.outlineView;

import java.util.List;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Comment;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeSearcher;
import org.key_project.jmlediting.core.dom.INodeTraverser;


public class JMLComents implements IASTNode{

   Comment node;
   String text;
   String type;
   
   public JMLComents(String commenttext,Comment node,String type) {
      text= commenttext;
      this.node = node;
      this.type = type;
   }
   @Override
   public String toString() {
      // TODO Auto-generated method stub
      return text;
   }
   public ASTNode getASTNode() {
      return node;
   }
   public ASTNode getParent() {
      return node.getAlternateRoot();
   }
   @Override
   public int getStartOffset() {
      // TODO Auto-generated method stub
      return node.getStartPosition();
   }
   @Override
   public int getEndOffset() {
      // TODO Auto-generated method stub
      return node.getLength()+node.getStartPosition();
   }
   @Override
   public boolean containsOffset(int offset) {
      // TODO Auto-generated method stub
      return false;
   }
   @Override
   public boolean containsCaret(int caretPosition) {
      // TODO Auto-generated method stub
      return false;
   }
   @Override
   public int getType() {
      // TODO Auto-generated method stub
      return 0;
   }
   @Override
   public List<IASTNode> getChildren() {
      // TODO Auto-generated method stub
      return null;
   }
   @Override
   public <T> T search(INodeSearcher<T> searcher) {
      // TODO Auto-generated method stub
      return null;
   }
   @Override
   public <T> T traverse(INodeTraverser<T> traverser, T init) {
      // TODO Auto-generated method stub
      return null;
   }
   @Override
   public String prettyPrintAST() {
      // TODO Auto-generated method stub
      return text;
   }
   
}
