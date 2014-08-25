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

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IMarkerDelta;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Platform;
import org.eclipse.debug.core.DebugEvent;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.IMemoryBlock;
import org.eclipse.debug.core.model.IProcess;
import org.eclipse.debug.core.model.ISourceLocator;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IThread;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.annotation.impl.BreakpointAnnotation;
import org.key_project.sed.core.annotation.impl.BreakpointAnnotationLink;
import org.key_project.sed.core.annotation.impl.BreakpointAnnotationType;
import org.key_project.sed.core.model.ISEDDebugElement;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.event.ISEDAnnotationListener;
import org.key_project.sed.core.model.event.SEDAnnotationEvent;
import org.key_project.sed.core.provider.SEDDebugTargetContentProvider;
import org.key_project.sed.core.sourcesummary.ISEDSourceModel;
import org.key_project.sed.core.sourcesummary.impl.SEDMemorySourceModel;
import org.key_project.sed.core.sourcesummary.impl.SEDMemorySourceRange;
import org.key_project.sed.core.sourcesummary.impl.SEDMemorySourceSummary;
import org.key_project.sed.core.util.ISEDIterator;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.sed.core.util.SEDAnnotationUtil;
import org.key_project.sed.core.util.SEDBreadthFirstIterator;
import org.key_project.sed.core.util.SEDPreorderIterator;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Provides a basic implementation of {@link ISEDDebugTarget}.
 * </p>
 * <p>
 * For each {@link ISEDDebugNode} as child of this {@link ISEDDebugTarget}
 * {@link #addToSourceModel(ISEDDebugNode)} has to be called to ensure
 * that the {@link ISEDDebugNode} is part of the {@link ISEDSourceModel} ({@link #getSourceModel()}).
 * </p>
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
    * The used {@link ISEDSourceModel}.
    */
   private final SEDMemorySourceModel sourceModel = new SEDMemorySourceModel();

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
   public AbstractSEDDebugTarget getDebugTarget() {
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
      try {
         return ArrayUtil.search(getSymbolicThreads(), new IFilter<ISEDThread>() {
            @Override
            public boolean select(ISEDThread element) {
               return !element.isSuspended();
            }
         }) == null;
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         return false;
      }
   }
   
   /**
    * This method should be called after an {@link ISEDThread} is resumed.
    * @param thread The resumed {@link ISEDThread}.
    */
   public void threadResumed(ISEDThread thread) {
      if (!isSuspended()) {
         fireResumeEvent(DebugEvent.CLIENT_REQUEST);
      }
   }
   
   /**
    * This method should be called after an {@link ISEDThread} is suspended.
    * @param thread The suspended {@link ISEDThread}.
    */
   public void threadSuspended(ISEDThread thread) {
      if (isSuspended()) {
         fireSuspendEvent(DebugEvent.CLIENT_REQUEST);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      ISEDThread[] threads = getSymbolicThreads();
      for (ISEDThread thread : threads) {
         thread.resume();
      }
      fireResumeEvent(DebugEvent.CLIENT_REQUEST);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      ISEDThread[] threads = getSymbolicThreads();
      for (ISEDThread thread : threads) {
         thread.suspend();
      }
      fireSuspendEvent(DebugEvent.CLIENT_REQUEST);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointAdded(IBreakpoint breakpoint) {
      try {
         // Add annotation if required
         if (!updateBreakpointAnnotation()) {
            // Update links if annotation was already present
            updateBreakpointAnnotationLinks(breakpoint);
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointChanged(IBreakpoint breakpoint, IMarkerDelta delta) {
      try {
         // Add annotation if required
         if (!updateBreakpointAnnotation()) {
            // Update links if annotation was already present
            updateBreakpointAnnotationLinks(breakpoint);
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void breakpointRemoved(IBreakpoint breakpoint, IMarkerDelta delta) {
      try {
         // Remove annotation if required
         if (!updateBreakpointAnnotation()) {
            // If annotation was not removed remove all links of the given breakpoint.
            ISEDAnnotationType breakpointType = SEDAnnotationUtil.getAnnotationtype(BreakpointAnnotationType.TYPE_ID);
            ISEDAnnotation[] annotations = getRegisteredAnnotations(breakpointType);
            for (ISEDAnnotation annotation : annotations) {
               ISEDAnnotationLink[] links = annotation.getLinks();
               for (ISEDAnnotationLink link : links) {
                  if (link instanceof BreakpointAnnotationLink) {
                     BreakpointAnnotationLink blink = (BreakpointAnnotationLink)link;
                     if (blink.getBreakpoint() == breakpoint) {
                        annotation.removeLink(blink);
                     }
                  }
               }
            }
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }
   }
   
   /**
    * Adds all Breakpoints to this {@link ISEDDebugTarget}. 
    * Is called only when the {@link ISEDDebugTarget} is initially created.
    */
   protected void initBreakpoints() throws DebugException {
      IBreakpoint[] breakpoints = DebugPlugin.getDefault().getBreakpointManager().getBreakpoints();     
      // Initialize all available breakpoints
      for(int i = 0; i < breakpoints.length; i++){
         initBreakpoint(breakpoints[i]);
      }
      // Add breakpoint annotation if at least one breakpoint is supported
      updateBreakpointAnnotation();
   }
   
   /**
    * Adds the given {@link IBreakpoint} to this {@link ISEDDebugTarget}.
    * @param breakpoints The initial {@link IBreakpoint}s.
    */
   protected abstract void initBreakpoint(IBreakpoint breakpoint) throws DebugException;
   
   /**
    * Ensures that this {@link ISEDDebugTarget} has a {@link BreakpointAnnotation}
    * only if at least one breakpoint is supported and returned via {@link #getBreakpoints()}.
    * @return {@code true} if annotation was added or removed, {@code false} if nothing has changed
    */
   protected boolean updateBreakpointAnnotation() throws DebugException {
      ISEDAnnotationType breakpointType = SEDAnnotationUtil.getAnnotationtype(BreakpointAnnotationType.TYPE_ID);
      ISEDAnnotation[] annotations = getRegisteredAnnotations(breakpointType);
      IBreakpoint[] supportedBreakpoints = getBreakpoints();
      if (!ArrayUtil.isEmpty(supportedBreakpoints)) {
         if (ArrayUtil.isEmpty(annotations)) {
            // Add annotation
            ISEDAnnotation breakpointAnnotation = breakpointType.createAnnotation();
            registerAnnotation(breakpointAnnotation);
            // Add annotation links
            ISEDIterator iterator = new SEDBreadthFirstIterator(this);
            while (iterator.hasNext()) {
               ISEDDebugElement next = iterator.next();
               if (next instanceof ISEDDebugNode) {
                  breakpointType.initializeNode((ISEDDebugNode)next, breakpointAnnotation);
               }
            }
            return true;
         }
         else {
            return false;
         }
      }
      else {
         if (!ArrayUtil.isEmpty(annotations)) {
            for (ISEDAnnotation annotation : annotations) {
               unregisterAnnotation(annotation);
            }
            return true;
         }
         else {
            return false;
         }
      }
   }

   /**
    * Updates the available {@link BreakpointAnnotationLink}s.
    * @param breakpoint The {@link IBreakpoint} to update.
    * @throws DebugException Occurred Exception.
    */
   protected void updateBreakpointAnnotationLinks(IBreakpoint breakpoint) throws DebugException {
      try {
         BreakpointAnnotationType breakpointType = (BreakpointAnnotationType)SEDAnnotationUtil.getAnnotationtype(BreakpointAnnotationType.TYPE_ID);
         ISEDIterator iterator = new SEDBreadthFirstIterator(this);
         while (iterator.hasNext()) {
            ISEDDebugElement next = iterator.next();
            if (next instanceof ISEDDebugNode) {
               ISEDDebugNode node = (ISEDDebugNode)next;
               boolean hit = breakpoint.isEnabled() && checkBreakpointHit(breakpoint, node);
               if (hit) {
                  ISEDAnnotationLink[] links = node.getAnnotationLinks(breakpointType);
                  boolean found = false;
                  for (ISEDAnnotationLink link : links) {
                     if (breakpointType.isBreakpointLink(link, breakpoint)) {
                        found = true;
                        ((BreakpointAnnotationLink)link).updateBreakpointName();
                     }
                  }
                  if (!found) {
                     ISEDAnnotation[] annotations = getRegisteredAnnotations(breakpointType);
                     for (ISEDAnnotation annotation : annotations) {
                        breakpointType.addBreakpointLink(node, annotation, breakpoint);
                     }
                  }
               }
               else {
                  // Remove may available links of the given breakpoint
                  ISEDAnnotationLink[] links = node.getAnnotationLinks(breakpointType);
                  for (ISEDAnnotationLink link : links) {
                     if (breakpointType.isBreakpointLink(link, breakpoint)) {
                        node.removeAnnotationLink(link);
                     }
                  }
               }
            }
         }
      }
      catch (CoreException e) {
         throw new DebugException(e.getStatus());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IBreakpoint[] computeHitBreakpoints(ISEDDebugNode node) throws DebugException {
      try {
         List<IBreakpoint> result = new LinkedList<IBreakpoint>();
         IBreakpoint[] supportedBreakpoints = getBreakpoints();
         if (supportedBreakpoints != null) {
            for (IBreakpoint breakpoint : supportedBreakpoints) {
               if (breakpoint.isEnabled() && checkBreakpointHit(breakpoint, node)) {
                  result.add(breakpoint);
               }
            }
         }
         return result.toArray(new IBreakpoint[result.size()]);
      }
      catch (CoreException e) {
         throw new DebugException(e.getStatus());
      }
   }
   
   /**
    * Checks if the given {@link IBreakpoint} is fulfilled in the given {@link ISEDDebugNode}.
    * @param breakpoint The {@link IBreakpoint} to check.
    * @param node the {@link ISEDDebugNode} to check.
    * @return {@code true} hit, {@code false} not hit.
    */
   protected abstract boolean checkBreakpointHit(IBreakpoint breakpoint, ISEDDebugNode node);

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
   public Map<String, String> computeStatistics(IProgressMonitor monitor) throws DebugException {
      // Compute statistics
      if (monitor == null) {
         monitor = new NullProgressMonitor();
      }
      monitor.beginTask("Computing statistics", IProgressMonitor.UNKNOWN);
      SWTUtil.checkCanceled(monitor);
      int nodeCount = 0;
      int splitCount = 0;
      int terminatedBranchesCount = 0;
      int notTerminatedBranchesCount = 0;
      ISEDIterator iter = new SEDPreorderIterator(this);
      while (iter.hasNext()) {
         SWTUtil.checkCanceled(monitor);
         ISEDDebugElement next = iter.next();
         if (next instanceof ISEDDebugNode) {
            ISEDDebugNode node = (ISEDDebugNode)next;
            nodeCount++;
            ISEDDebugNode[] children = node.getChildren();
            if (children.length == 0) {
               if (node instanceof ISEDTermination) {
                  terminatedBranchesCount++;
               }
               else {
                  notTerminatedBranchesCount++;
               }
            }
            else if (children.length >= 2) {
               splitCount++;
            }
         }
         monitor.worked(1);
      }
      // Create result
      Map<String, String> statistics = new LinkedHashMap<String, String>();
      statistics.put("Number of nodes", nodeCount + "");
      statistics.put("Number of splits", splitCount + "");
      statistics.put("Number of completed paths", terminatedBranchesCount + "");
      statistics.put("Number of not completed paths", notTerminatedBranchesCount + "");
      monitor.done();
      return statistics;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEDMemorySourceModel getSourceModel() {
      return sourceModel;
   }
   
   /**
    * This method has to be called once for each {@link ISEDDebugNode}
    * to add it to the {@link ISEDSourceModel}.
    * @param node The new {@link ISEDDebugNode} to add to the {@link ISEDSourceModel}.
    * @throws DebugException Occurred Exception.
    */
   protected void addToSourceModel(ISEDDebugNode node) throws DebugException {
      if (node instanceof IStackFrame && getLaunch() != null) {
         IStackFrame stackFrame = (IStackFrame)node;
         ISourceLocator locator = getLaunch().getSourceLocator();
         if (locator != null) {
            Object source = locator.getSourceElement(stackFrame);
            if (source != null) {
               SEDMemorySourceSummary summary = sourceModel.getSourceSummary(source);
               if (summary == null) {
                  summary = new SEDMemorySourceSummary(source);
                  sourceModel.addSourceSummary(summary);
               }
               int lineNumber = stackFrame.getLineNumber();
               int charStart = stackFrame.getCharStart();
               int charEnd = stackFrame.getCharEnd();
               SEDMemorySourceRange range = summary.getSourceRange(lineNumber, charStart, charEnd);
               if (range == null) {
                  range = new SEDMemorySourceRange(lineNumber, charStart, charEnd);
                  summary.addSourceRange(range);
               }
               range.addDebugNode(node);
            }
         }
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