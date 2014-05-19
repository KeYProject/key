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

package org.key_project.sed.core.model.impl;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IMemoryBlock;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.IThread;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.event.ISEDAnnotationListener;
import org.key_project.sed.core.model.event.SEDAnnotationEvent;
import org.key_project.sed.core.provider.SEDDebugTargetContentProvider;
import org.key_project.util.java.ObjectUtil;

/**
 * Provides a basic implementation of {@link ISEDDebugTarget}.
 * @author Martin Hentschel
 * @see ISEDDebugTarget
 */
@SuppressWarnings("restriction")
public abstract class AbstractSEDDebugTarget extends AbstractSEDDebugElement implements ISEDDebugTarget {
   /**
    * Is this {@link ISEDDebugTarget} executable meaning that
    * suspend, resume, step operations and disconnect are supported?;
    */
   private final boolean executable;
   
   /**
    * The {@link ILaunch} in that this {@link IDebugTarget} is used.
    */
   private final ILaunch launch;
   
   /**
    * Indicates that the connection to the process is disconnected or not.
    */
   private boolean disconnected = false;
   
   /**
    * Indicates that the process is currently suspended or not.
    */
   private boolean suspended = true;

   /**
    * Indicates that the process is termianted or not.
    */
   private boolean terminated = false;
   
   /**
    * The defined model identifier.
    */
   private String modelIdentifier;

   /**
    * The name of this debug target.
    */
   private String name;
   
   /**
    * All registered annotations.
    */
   private final List<ISEDAnnotation> registeredAnnotations = new LinkedList<ISEDAnnotation>();
   
   /**
    * All registered {@link ISEDAnnotationListener}.
    */
   private final List<ISEDAnnotationListener> annotationListener = new LinkedList<ISEDAnnotationListener>();
   
   /**
    * Constructor.
    * @param launch The {@link ILaunch} in that this {@link IDebugTarget} is used.
    * @param executable {@code true} Support suspend, resume, etc.; {@code false} Do not support suspend, resume, etc.
    */
   public AbstractSEDDebugTarget(ILaunch launch, boolean executable) {
      super(null);
      this.executable = executable;
      this.launch = launch;
      
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugTarget getDebugTarget() {
      return this;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getModelIdentifier() {
      return modelIdentifier;
   }
   
   /**
    * Sets the unique model identifier.
    * @param modelIdentifier The unique model identifier to set.
    */
   protected void setModelIdentifier(String modelIdentifier) {
      this.modelIdentifier = modelIdentifier;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ILaunch getLaunch() {
      return launch;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public IThread[] getThreads() throws DebugException {
      return new IThread[0];
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean hasThreads() throws DebugException {
      IThread[] threads = getThreads();
      return threads != null && threads.length >= 1;
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Class adapter) {
      if (IElementContentProvider.class.equals(adapter)) {
         // Change used content provider to show SED specific children instead of the default one from the debug API.
         return SEDDebugTargetContentProvider.getDefaultInstance();
      }
      else {
         return Platform.getAdapterManager().getAdapter(this, adapter);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean supportsBreakpoint(IBreakpoint breakpoint) {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProcess getProcess() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canTerminate() {
      return !isTerminated();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isTerminated() {
      return terminated;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void terminate() throws DebugException {
      terminated = true;
      fireTerminateEvent();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canResume() {
      return executable && isSuspended() && !isTerminated() && !isDisconnected();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canSuspend() {
      return executable && !isSuspended() && !isTerminated() && !isDisconnected();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isSuspended() {
      return suspended;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      suspended = false;
      fireResumeEvent(DebugEvent.RESUME);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      suspended = true;
      fireSuspendEvent(DebugEvent.SUSPEND);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointAdded(IBreakpoint breakpoint) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointRemoved(IBreakpoint breakpoint, IMarkerDelta delta) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointChanged(IBreakpoint breakpoint, IMarkerDelta delta) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDisconnect() {
      return executable && !isDisconnected() && !isTerminated();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void disconnect() throws DebugException {
      this.disconnected = true;
      fireTerminateEvent(); // Disconnected threads are treated as terminated by the Eclipse Debug API.
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDisconnected() {
      return disconnected;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean supportsStorageRetrieval() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IMemoryBlock getMemoryBlock(long startAddress, long length) throws DebugException {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() throws DebugException {
      return name;
   }

   /**
    * Sets the name of this debug target.
    * @param name The name to set.
    */
   protected void setName(String name) {
      this.name = name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void registerAnnotation(ISEDAnnotation annotation) {
      if (annotation != null && !registeredAnnotations.contains(annotation)) {
         if (registeredAnnotations.add(annotation)) {
            fireAnnotationRegistered(new SEDAnnotationEvent(this, annotation));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void unregisterAnnotation(ISEDAnnotation annotation) {
      if (annotation != null) {
         if (registeredAnnotations.remove(annotation)) {
            ISEDAnnotationLink[] links = annotation.getLinks();
            for (ISEDAnnotationLink link : links) {
               link.getTarget().removeAnnotationLink(link);
            }
            fireAnnotationUnregistered(new SEDAnnotationEvent(this, annotation));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotation[] getRegisteredAnnotations() {
      return registeredAnnotations.toArray(new ISEDAnnotation[registeredAnnotations.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotation[] getRegisteredAnnotations(ISEDAnnotationType type) {
      List<ISEDAnnotation> result = new LinkedList<ISEDAnnotation>();
      for (ISEDAnnotation annotation : registeredAnnotations) {
         if (ObjectUtil.equals(type, annotation.getType())) {
            result.add(annotation);
         }
      }
      return result.toArray(new ISEDAnnotation[result.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isRegistered(ISEDAnnotation annotation) {
      return annotation != null && registeredAnnotations.contains(annotation);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void moveRegisteredAnnotation(ISEDAnnotation annotation, int newIndex) {
      if (annotation != null && newIndex >= 0 && newIndex < registeredAnnotations.size()) {
         if (registeredAnnotations.remove(annotation)) {
            registeredAnnotations.add(newIndex, annotation);
            fireAnnotationMoved(new SEDAnnotationEvent(this, annotation));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int indexOfRegisteredAnnotation(ISEDAnnotation annotation) {
      if (annotation != null) {
         return registeredAnnotations.indexOf(annotation);
      }
      else {
         return -1;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int countRegisteredAnnotations() {
      return registeredAnnotations.size();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addAnnotationListener(ISEDAnnotationListener l) {
      if (l != null) {
         annotationListener.add(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeAnnotationListener(ISEDAnnotationListener l) {
      if (l != null) {
         annotationListener.remove(l);
      }
   }
   
   /**
    * Fires the event {@link ISEDAnnotationListener#annotationRegistered(SEDAnnotationEvent)}.
    * @param e The {@link SEDAnnotationEvent}.
    */
   protected void fireAnnotationRegistered(SEDAnnotationEvent e) {
      ISEDAnnotationListener[] listener = annotationListener.toArray(new ISEDAnnotationListener[annotationListener.size()]);
      for (ISEDAnnotationListener l : listener) {
         l.annotationRegistered(e);
      }
   }
   
   /**
    * Fires the event {@link ISEDAnnotationListener#annotationUnregistered(SEDAnnotationEvent)}.
    * @param e The {@link SEDAnnotationEvent}.
    */
   protected void fireAnnotationUnregistered(SEDAnnotationEvent e) {
      ISEDAnnotationListener[] listener = annotationListener.toArray(new ISEDAnnotationListener[annotationListener.size()]);
      for (ISEDAnnotationListener l : listener) {
         l.annotationUnregistered(e);
      }
   }
   
   /**
    * Fires the event {@link ISEDAnnotationListener#annotationMoved(SEDAnnotationEvent)}.
    * @param e The {@link SEDAnnotationEvent}.
    */
   protected void fireAnnotationMoved(SEDAnnotationEvent e) {
      ISEDAnnotationListener[] listener = annotationListener.toArray(new ISEDAnnotationListener[annotationListener.size()]);
      for (ISEDAnnotationListener l : listener) {
         l.annotationMoved(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      try {
         return getName();
      }
      catch (DebugException e) {
         return e.getMessage();
      }
   }
}