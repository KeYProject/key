package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDGroupable;

/**
 * Defines the public methods to edit an {@link ISEDGroupable} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEDMemoryGroupable extends ISEDGroupable {
   /**
    * Defines if this {@link ISEDDebugNode} is groupable or not.
    * @param groupable {@code true} is groupable, {@code false} is not groupable.
    */
   public void setGroupable(boolean groupable);
   
   /**
    * Adds a new group end condition.
    * @param groupEndCondition The method group end condition to add.
    */
   public void addGroupEndCondition(ISEDBranchCondition groupEndCondition);
}
