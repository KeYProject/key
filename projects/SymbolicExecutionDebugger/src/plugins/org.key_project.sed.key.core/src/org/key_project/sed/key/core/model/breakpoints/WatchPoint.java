package org.key_project.sed.key.core.model.breakpoints;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaWatchpoint;


@SuppressWarnings("restriction")
public class WatchPoint extends JavaWatchpoint {
   
   private String condition;


   public static final String KEY_WATCHPOINT= "org.key_project.sed.key.ui.breakpoints.watchpointMarker";

   public WatchPoint() {
      try {
         IMarker marker = ResourcesPlugin.getWorkspace().getRoot().createMarker(KEY_WATCHPOINT);
         setMarker(marker);
         setHitCount(-1);
         setSuspendPolicy(SUSPEND_THREAD);
         setTypeName("KeYWatchpoint");
         setEnabled(true);
         DebugPlugin.getDefault().getBreakpointManager().addBreakpoint(this);
      }
      catch (CoreException e1) {
         e1.printStackTrace();
      }
   }

   @Override
   public String getFieldName() throws CoreException {
      return "condition";
   }
   
   @Override
   public void setEnabled(boolean enabled) throws CoreException {
      super.setEnabled(enabled);
      setAccess(false);
      setModification(false);
   }
   
   @Override
   public void setAccess(boolean access) throws CoreException {
      if (access == isAccess()) {
         return;
      }     
      setAttribute(ACCESS, access);
      recreate();
   }
   
   @Override
   public void setModification(boolean modification) throws CoreException {
      if (modification == isModification()) {
         return;
      }
      setAttribute(MODIFICATION, modification);
      recreate();
   }
   
   public String getCondition() {
      return condition;
   }

   public void setCondition(String condition) {
      this.condition = condition;
   }
   
   

}
