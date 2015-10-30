package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEBranchCondition;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEGroupable;

/**
 * Defines the public methods to edit an {@link ISEGroupable} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEMemoryGroupable extends ISEGroupable {
   /**
    * Defines if this {@link ISENode} is groupable or not.
    * @param groupable {@code true} is groupable, {@code false} is not groupable.
    */
   public void setGroupable(boolean groupable);
   
   /**
    * Adds a new group end condition.
    * @param groupEndCondition The method group end condition to add.
    */
   public void addGroupEndCondition(ISEBranchCondition groupEndCondition);
}
