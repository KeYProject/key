package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Defines the public methods to edit an {@link ISEDDebugNode} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEDMemoryDebugNode extends ISEDDebugNode {
   /**
    * Sets the name of this node.
    * @param name the name to set.
    */
   public void setName(String name);
   
   /**
    * Adds a new {@link ISEDDebugNode} child node.
    * @param child The {@link ISEDDebugNode} to add.
    */
   public void addChild(ISEDDebugNode child);
}
