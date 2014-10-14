package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDGroupable;

/**
 * Defines the public methods to edit an {@link ISEDGroupable} in
 * the main memory.
 * @author Martin Hentschel
 */
public interface ISEDMemoryGroupable extends ISEDGroupable {
   /**
    * Adds a new group end condition.
    * @param groupEndCondition The method group end condition to add.
    */
   public void addGroupEndCondition(ISEDBranchCondition groupEndCondition);
}
