/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.ui.propertyPages;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.jdt.debug.core.IJavaBreakpoint;
import org.eclipse.jdt.internal.debug.ui.breakpoints.AbstractJavaBreakpointEditor;
import org.eclipse.jdt.internal.debug.ui.breakpoints.CompositeBreakpointEditor;
import org.eclipse.jdt.internal.debug.ui.breakpoints.StandardJavaBreakpointEditor;
import org.eclipse.jdt.internal.debug.ui.propertypages.JavaBreakpointPage;
import org.eclipse.jdt.internal.debug.ui.propertypages.PropertyPageMessages;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.IWorkbenchPropertyPage;
import org.key_project.sed.key.core.breakpoints.KeYWatchpoint;
import org.key_project.sed.key.ui.editors.KeYWatchpointConditionEditor;

/**
 * This class defines the property page that is displayed when editing the properties of a KeY Watchpoint
 * 
 * @author Marco Drebing
 */
@SuppressWarnings("restriction")
public class WatchpointPropertyPage extends JavaBreakpointPage implements
      IWorkbenchPropertyPage {

   private AbstractJavaBreakpointEditor fEditor;
   
   public WatchpointPropertyPage() {
      super();
   }
   
   @Override
   protected void createTypeSpecificEditors(Composite parent) {
      try {
      String type = getBreakpoint().getMarker().getType();
      if (KeYWatchpoint.KEY_WATCHPOINT.equals(type)) {
         setTitle(PropertyPageMessages.JavaLineBreakpointPage_20);
         fEditor = new CompositeBreakpointEditor(new AbstractJavaBreakpointEditor[] 
             {new StandardJavaBreakpointEditor(), new KeYWatchpointConditionEditor()});
      } else {
         // use standard editor for any other kind of breakpoint (@see bug 325161)
         fEditor = new StandardJavaBreakpointEditor();
      }
      fEditor.createControl(parent);
      fEditor.addPropertyListener(new IPropertyListener() {
         public void propertyChanged(Object source, int propId) {
            IStatus status = fEditor.getStatus();
            if (status.isOK()) {
               if (fPrevMessage != null) {
                  removeErrorMessage(fPrevMessage);
                  fPrevMessage = null;
               }
            } else {
               fPrevMessage = status.getMessage();
               addErrorMessage(fPrevMessage);
            }
         }
      });
      fEditor.setInput(getBreakpoint());
   } catch (CoreException e) {
      setErrorMessage(e.getMessage());
   }
   }
   

   /**
    * Stores the values configured in this page. This method
    * should be called from within a workspace runnable to
    * reduce the number of resource deltas.
    * @throws CoreException if an exception occurs
    */
   protected void doStore() throws CoreException {
      IJavaBreakpoint breakpoint = getBreakpoint();
      storeEnabled(breakpoint);
      if (fEditor.isDirty()) {
         fEditor.doSave();
      }
   }

   /**
    * Stores the value of the enabled state in the breakpoint.
    * @param breakpoint the breakpoint to update
    * @throws CoreException if an exception occurs while setting
    *  the enabled state
    */
   private void storeEnabled(IJavaBreakpoint breakpoint) throws CoreException {
      breakpoint.setEnabled(fEnabledButton.getSelection());
   }

}