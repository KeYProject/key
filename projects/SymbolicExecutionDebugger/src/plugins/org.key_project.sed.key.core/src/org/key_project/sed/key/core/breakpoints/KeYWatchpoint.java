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

package org.key_project.sed.key.core.breakpoints;

import org.eclipse.core.resources.IMarker;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.internal.debug.core.breakpoints.JavaBreakpoint;
import org.eclipse.jdt.internal.debug.core.model.JDIDebugTarget;
import org.key_project.sed.key.core.model.KeYDebugTarget;

import com.sun.jdi.ObjectReference;
import com.sun.jdi.ReferenceType;
import com.sun.jdi.ThreadReference;
import com.sun.jdi.request.EventRequest;

@SuppressWarnings("restriction")
public class KeYWatchpoint extends JavaBreakpoint {
   
   protected static final String CONDITION = "org.key_project.sed.key.core.condition"; 
   
   protected static final String CONDITION_ENABLED = "org.key_project.sed.key.core.conditionEnabled"; 
   
   protected static final String TYPE = "org.key_project.sed.key.core.conditionEnabled"; 
   
   public static final String KEY_WATCHPOINT = "org.key_project.sed.key.ui.breakpointMarkers.watchpointMarker";

   private static final String SUSPEND = "org.key_project.sed.key.core.suspend";
   
   public KeYWatchpoint(){
      super();
   }
   
   public KeYWatchpoint(IType type, String condition) {
      try {
         IMarker marker = type.getResource().createMarker(KEY_WATCHPOINT);
         setMarker(marker);
         ensureMarker().setAttribute(IBreakpoint.ID, KEY_WATCHPOINT);
         setSuspendPolicy(SUSPEND_THREAD);
         setEnabled(true);
         setTypeName(type.getElementName());
         setCondition(condition);
         register(true);
         setSuspendOnTrue(true);
      }
      catch (CoreException e1) {
         e1.printStackTrace();
      }
   }
   
   public boolean supportsCondition(){
      return true;
   }
   
   @Override
   public String getModelIdentifier() {
      return KeYDebugTarget.MODEL_IDENTIFIER;
   }

   @Override
   protected void addInstanceFilter(EventRequest request, ObjectReference object) {
      
   }

   @Override
   protected EventRequest[] newRequests(JDIDebugTarget target,
         ReferenceType type) throws CoreException {
      return null;
   }

   @Override
   protected void setRequestThreadFilter(EventRequest request,
         ThreadReference thread) {
      
   }

   public String getCondition() throws CoreException {
         return (String) ensureMarker().getAttribute(CONDITION, null);
   }

   public void setCondition(String condition) throws CoreException {
      ensureMarker().setAttribute(CONDITION, condition);
   }

   public boolean isConditionEnabled() throws DebugException {
      return ensureMarker().getAttribute(CONDITION_ENABLED, true);
   }

   public void setConditionEnabled(boolean conditionEnabled) throws CoreException {
      ensureMarker().setAttribute(CONDITION_ENABLED, true);
   }

   public IType getType() throws CoreException {
      ICompilationUnit icu = (ICompilationUnit) JavaCore.create(ensureMarker().getResource());
      return icu.getType(getTypeName());
   }

   public boolean isSuspendOnTrue() throws DebugException {
      return ensureMarker().getAttribute(SUSPEND, true);
   }

   public void setSuspendOnTrue(boolean suspendOnTrue) throws CoreException {
      ensureMarker().setAttribute(SUSPEND, suspendOnTrue);
   }
}