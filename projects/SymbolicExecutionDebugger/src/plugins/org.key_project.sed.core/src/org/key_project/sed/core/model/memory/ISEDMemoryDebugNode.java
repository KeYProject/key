package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Defines the public methods to edit an {@link ISEDDebugNode} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEDMemoryDebugNode extends ISEDDebugNode {
   /**
    * Sets the unique ID.
    * @param id The new unique ID to use.
    */
   public void setId(String id);
   
   /**
    * Sets the name of this node.
    * @param name the name to set.
    */
   public void setName(String name);
   
   /**
    * Sets the path condition.
    * @param pathCondtion The path condition to set.
    */
   public void setPathCondition(String pathCondition);
   
   /**
    * Adds a new {@link ISEDDebugNode} child node.
    * @param child The {@link ISEDDebugNode} to add.
    */
   public void addChild(ISEDDebugNode child);
   
   /**
    * Adds a new {@link ISEDDebugNode} child node.
    * @param index The index to insert the new child at.
    * @param child The {@link ISEDDebugNode} to add.
    */
   public void addChild(int index, ISEDDebugNode child);
   
   /**
    * Removes the child {@link ISEDDebugNode}.
    * @param child The {@link ISEDDebugNode} to remove.
    */
   public void removeChild(ISEDDebugNode child);
   
   /**
    * Returns the index of the given child {@link ISEDDebugNode}.
    * @param child The child {@link ISEDDebugNode}.
    * @return The index of the child {@link ISEDDebugNode} or {@code -1} if it is no child.
    */
   public int indexOfChild(ISEDDebugNode child);
}
