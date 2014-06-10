package org.key_project.sed.core.annotation.impl;

import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.IDebugModelPresentation;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * An {@link ISEDAnnotationLink} which contains the fulfilling breakpoint.
 * @author Martin Hentschel
 */
public class BreakpointAnnotationLink extends AbstractSEDAnnotationLink {
   /**
    * Property {@link #getBreakpoint()}.
    */
   public static final String PROP_BREAKPOINT = "breakpoint";
   
   /**
    * Property {@link #getBreakpointName()}.
    */
   public static final String PROP_BREAKPOINT_NAME = "breakpointName";
   
   /**
    * The breakpoint.
    */
   private IBreakpoint breakpoint;
   
   /**
    * The name of this breakpoint.
    */
   private String breakpointName;
   
   /**
    * Constructor.
    * @param source The source {@link ISEDAnnotation}.
    * @param target The target {@link ISEDDebugNode}.
    */
   public BreakpointAnnotationLink(ISEDAnnotation source, ISEDDebugNode target) {
      super(source, target);
   }

   /**
    * Returns the breakpoint.
    * @return The breakpoint.
    */
   public IBreakpoint getBreakpoint() {
      return breakpoint;
   }

   /**
    * Sets the breakpoint.
    * @param breakpoint The breakpoint to set.
    */
   public void setBreakpoint(IBreakpoint breakpoint) {
      IBreakpoint oldValue = getBreakpoint();
      this.breakpoint = breakpoint;
      firePropertyChange(PROP_BREAKPOINT, oldValue, getBreakpoint());
      updateBreakpointName();
   }
   
   /**
    * Updates {@link #getBreakpointName()} according to {@link #getBreakpoint()}.
    */
   public void updateBreakpointName() {
      setBreakpointName(computeBreakpointName());
   }
   
   /**
    * Computes the name of the {@link IBreakpoint}.
    * @return The computed breakpoint name.
    */
   protected String computeBreakpointName() {
      if (breakpoint != null) {
         IDebugModelPresentation debugModelPresentation = DebugUITools.newDebugModelPresentation();
         try {
            return debugModelPresentation.getText(breakpoint);
         }
         finally {
            debugModelPresentation.dispose();
         }
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the human readable name of {@link #getBreakpoint()}.
    * @return The human readable name or {@code null} if not available.
    */
   public String getBreakpointName() {
      return breakpointName;
   }
   
   /**
    * Defines the human readable name of {@link #getBreakpoint()}.
    * @param breakpointName The name to set.
    */
   public void setBreakpointName(String breakpointName) {
      String oldValue = getBreakpointName();
      this.breakpointName = breakpointName;
      firePropertyChange(PROP_BREAKPOINT_NAME, oldValue, getBreakpointName());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete() {
      return breakpoint == null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void delete() {
      // Remove link
      super.delete();
      // Remove annotation if no links are available
      if (!getSource().hasLinks()) {
         getTarget().getDebugTarget().unregisterAnnotation(getSource());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getBreakpointName();
   }
}
