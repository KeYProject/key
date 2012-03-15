package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * Defines the public methods to edit an {@link ISEDDebugNode} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEDMemoryDebugNode extends ISEDDebugNode {
   /**
    * Adds a new {@link ISEDDebugNode} child node.
    * @param child The {@link ISEDDebugNode} to add.
    */
   public void addChild(ISEDDebugNode child);
}
