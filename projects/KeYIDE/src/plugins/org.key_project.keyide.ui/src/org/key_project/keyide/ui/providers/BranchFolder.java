package org.key_project.keyide.ui.providers;

import de.uka.ilkd.key.proof.Node;

public class BranchFolder {
   
   private Node child;
   
   private BranchFolder parent;
   
   private String label;
   
   private boolean isProved = false;
   
   // TODO: Why is the parent a branch folder? If I guess I expect that the parent is a Node. 
   public BranchFolder(BranchFolder parent, Node child, String label){
      this.parent = parent;
      this.child = child;
      this.label = label;
   }
   
   public Node getChild() {
      return child;
   }
   // TODO: I think this will never change? So remove setter.
   public void setChild(Node child) {
      this.child = child;
   }
   public BranchFolder getParent() {
      return parent;
   }
   // TODO: I think this will never change? So remove setter.
   public void setParent(BranchFolder parent) {
      this.parent = parent;
   }

   public String getLabel() {
      return label;
   }

   // TODO: I think this will never change? So remove setter.
   public void setLabel(String label) {
      this.label = label;
   }

   public boolean isProved() {
      return isProved;
   }

   public void setProved(boolean isProved) {
      this.isProved = isProved;
   }
      
}
