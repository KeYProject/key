package org.key_project.sed.core.model;

import org.eclipse.debug.core.DebugException;

/**
 * {@link ISEDDebugNode}s which realize this interface group children
 * and are collapsible. In the collapsed state only an {@link ISEDBranchCondition}
 * is shown between the start and each ending node.
 * <p>
 * The up to now discovered {@link ISEDDebugNode}s which completes the group
 * are accessible via {@link #getGroupEndConditions()}.
 * Backward navigation from an {@link ISEDDebugNode} to the groups it completes
 * is possible via {@link ISEDDebugNode#getGroupStartConditions()}
 * @author Martin Hentschel
 */
public interface ISEDGroupable {
   /**
    * Checks if this {@link ISEDDebugNode} is groupable or not.
    * @return {@code true} is groupable, {@code false} is not groupable.
    */
   public boolean isGroupable();
   
   /**
    * Checks if this {@link ISEDDebugNode} is collapsed.
    * @return {@code true} collapsed, {@code false} expanded (default state).
    */
   public boolean isCollapsed();
   
   /**
    * Defines if this {@link ISEDDebugNode} is collapsed.
    * @param collapsed {@code true} collapsed, {@code false} expanded (default state).
    */
   public void setCollapsed(boolean collapsed);
   
   /**
    * Returns the up to know discovered conditions when this {@link ISEDGroupable} is completed.
    * @return The up to know discovered conditions when this {@link ISEDGroupable} is completed.
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEDBranchCondition[] getGroupEndConditions() throws DebugException;
}
