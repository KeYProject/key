package org.key_project.keyide.ui.providers;

import de.uka.ilkd.key.proof.Node;

/**
 * A Class for the BranchFolers which are required for the correct tree visualization.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class BranchFolder {
   
   /**
    * The first child {@link Node} of this {@link BranchFolder}.
    */
   private Node child;
   
   /**
    * The Constructor
    * @param child - The first child {@link Node} of this {@link BranchFolder}.
    */
   public BranchFolder(Node child){
      this.child = child;
   }
   
   /**
    * Returns the first child {@link Node} of this {@link BranchFolder}.
    * @return The first child {@link Node} of this {@link BranchFolder}.
    */
   public Node getChild() {
      return child;
   }

   /**
    * Returns the label {@link String} of this {@link BranchFolder}. The label is the branchLabel of the child {@link Node}.
    * @return the label {@link String} of this {@link BranchFolder}.
    */
   public String getLabel() {
      return child.getNodeInfo().getBranchLabel();
   }

   /**
    * Returns true iff the first child {@link Node} is Closed. From this follows that this {@link BranchFolder} is closed. Otherwise false.
    * @return true iff the first child {@link Node} is Closed. From this follows that this {@link BranchFolder} is closed. Otherwise false.
    */
   public boolean isClosed() {
      return child.isClosed();
   }
      
}
