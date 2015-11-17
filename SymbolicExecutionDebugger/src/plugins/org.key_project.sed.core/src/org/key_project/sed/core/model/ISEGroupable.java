package org.key_project.sed.core.model;

import org.eclipse.debug.core.DebugException;

/**
 * {@link ISENode}s which realize this interface group children
 * and are collapsible. In the collapsed state only an {@link ISEBranchCondition}
 * is shown between the start and each ending node.
 * <p>
 * The up to now discovered {@link ISENode}s which completes the group
 * are accessible via {@link #getGroupEndConditions()}.
 * Backward navigation from an {@link ISENode} to the groups it completes
 * is possible via {@link ISENode#getGroupStartConditions()}
 * @author Martin Hentschel
 */
public interface ISEGroupable {
   /**
    * Checks if this {@link ISENode} is groupable or not.
    * @return {@code true} is groupable, {@code false} is not groupable.
    */
   public boolean isGroupable();
   
   /**
    * Checks if this {@link ISENode} is collapsed.
    * @return {@code true} collapsed, {@code false} expanded (default state).
    */
   public boolean isCollapsed();
   
   /**
    * Defines if this {@link ISENode} is collapsed.
    * @param collapsed {@code true} collapsed, {@code false} expanded (default state).
    */
   public void setCollapsed(boolean collapsed);
   
   /**
    * Returns the up to know discovered conditions when this {@link ISEGroupable} is completed.
    * @return The up to know discovered conditions when this {@link ISEGroupable} is completed.
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the VM.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li>
    */
   public ISEBranchCondition[] getGroupEndConditions() throws DebugException;
}
