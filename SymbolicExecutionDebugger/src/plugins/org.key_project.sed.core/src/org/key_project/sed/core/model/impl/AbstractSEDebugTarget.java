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
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.debug.internal.ui.viewers.model.provisional.IElementContentProvider;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.annotation.impl.BreakpointAnnotation;
import org.key_project.sed.core.annotation.impl.BreakpointAnnotationLink;
import org.key_project.sed.core.annotation.impl.BreakpointAnnotationType;
import org.key_project.sed.core.model.ISEDebugElement;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISETermination;
import org.key_project.sed.core.model.ISEThread;
import org.key_project.sed.core.model.event.ISEAnnotationListener;
import org.key_project.sed.core.model.event.SEAnnotationEvent;
import org.key_project.sed.core.provider.SEDebugTargetContentProvider;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.sed.core.sourcesummary.ISESourceModel;
import org.key_project.sed.core.sourcesummary.impl.SEMemorySourceModel;
import org.key_project.sed.core.sourcesummary.impl.SEMemorySourceRange;
import org.key_project.sed.core.sourcesummary.impl.SEMemorySourceSummary;
import org.key_project.sed.core.util.ISEIterator;
import org.key_project.sed.core.util.LogUtil;
import org.key_project.sed.core.util.SEAnnotationUtil;
import org.key_project.sed.core.util.SEBreadthFirstIterator;
import org.key_project.sed.core.util.SEPreorderIterator;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Provides a basic implementation of {@link ISEDebugTarget}.
 * </p>
 * <p>
 * For each {@link ISENode} as child of this {@link ISEDebugTarget}
 * {@link #addToSourceModel(ISENode)} has to be called to ensure
 * that the {@link ISENode} is part of the {@link ISESourceModel} ({@link #getSourceModel()}).
 * </p>
 * @author Martin Hentschel
 * @see ISEDebugTarget
 */
@SuppressWarnings("restriction")
public abstract class AbstractSEDebugTarget extends AbstractSEDebugElement implements ISEDebugTarget {
   /**
    * Is this {@link ISEDebugTarget} executable meaning that
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
   private final List<ISEAnnotation> registeredAnnotations = new LinkedList<ISEAnnotation>();
   
   /**
    * All registered {@link ISEAnnotationListener}.
    */
   private final List<ISEAnnotationListener> annotationListener = new LinkedList<ISEAnnotationListener>();
   
   /**
    * The used {@link ISESourceModel}.
    */
   private final SEMemorySourceModel sourceModel;

   /**
    * Constructor.
    * @param launch The {@link ILaunch} in that this {@link IDebugTarget} is used.
    * @param executable {@code true} Support suspend, resume, etc.; {@code false} Do not support suspend, resume, etc.
    * @param provideSourceModel {@code true} source model is available, {@code false} source model is not available.
    */
   public AbstractSEDebugTarget(ILaunch launch, boolean executable, boolean provideSourceModel) {
      super(null);
      this.executable = executable;
      this.launch = launch;
      this.sourceModel = provideSourceModel ? createSourceModel() : null;
   }

   /**
    * Creates the {@link SEMemorySourceModel} to use.
    * @return The {@link SEMemorySourceModel} to use.
    */
   protected SEMemorySourceModel createSourceModel() {
      return new SEMemorySourceModel(this);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public AbstractSEDebugTarget getDebugTarget() {
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
         return SEDebugTargetContentProvider.getDefaultInstance();
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
         return ArrayUtil.search(getSymbolicThreads(), new IFilter<ISEThread>() {
            @Override
            public boolean select(ISEThread element) {
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
    * {@inheritDoc}
    */
   @Override
   public void resume() throws DebugException {
      ISEThread[] threads = getSymbolicThreads();
      for (ISEThread thread : threads) {
         thread.resume();
      }
      fireResumeEvent(DebugEvent.CLIENT_REQUEST);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void suspend() throws DebugException {
      if (sourceModel != null) {
         sourceModel.setPossiblyIncomplete();
      }
      ISEThread[] threads = getSymbolicThreads();
      for (ISEThread thread : threads) {
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
            ISEAnnotationType breakpointType = SEAnnotationUtil.getAnnotationtype(BreakpointAnnotationType.TYPE_ID);
            ISEAnnotation[] annotations = getRegisteredAnnotations(breakpointType);
            for (ISEAnnotation annotation : annotations) {
               ISEAnnotationLink[] links = annotation.getLinks();
               for (ISEAnnotationLink link : links) {
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
    * Adds all Breakpoints to this {@link ISEDebugTarget}. 
    * Is called only when the {@link ISEDebugTarget} is initially created.
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
    * Adds the given {@link IBreakpoint} to this {@link ISEDebugTarget}.
    * @param breakpoints The initial {@link IBreakpoint}s.
    */
   protected abstract void initBreakpoint(IBreakpoint breakpoint) throws DebugException;
   
   /**
    * Ensures that this {@link ISEDebugTarget} has a {@link BreakpointAnnotation}
    * only if at least one breakpoint is supported and returned via {@link #getBreakpoints()}.
    * @return {@code true} if annotation was added or removed, {@code false} if nothing has changed
    */
   protected boolean updateBreakpointAnnotation() throws DebugException {
      ISEAnnotationType breakpointType = SEAnnotationUtil.getAnnotationtype(BreakpointAnnotationType.TYPE_ID);
      ISEAnnotation[] annotations = getRegisteredAnnotations(breakpointType);
      IBreakpoint[] supportedBreakpoints = getBreakpoints();
      if (!ArrayUtil.isEmpty(supportedBreakpoints)) {
         if (ArrayUtil.isEmpty(annotations)) {
            // Add annotation
            ISEAnnotation breakpointAnnotation = breakpointType.createAnnotation();
            registerAnnotation(breakpointAnnotation);
            // Add annotation links
            ISEIterator iterator = new SEBreadthFirstIterator(this);
            while (iterator.hasNext()) {
               ISEDebugElement next = iterator.next();
               if (next instanceof ISENode) {
                  breakpointType.initializeNode((ISENode)next, breakpointAnnotation);
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
            for (ISEAnnotation annotation : annotations) {
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
         BreakpointAnnotationType breakpointType = (BreakpointAnnotationType)SEAnnotationUtil.getAnnotationtype(BreakpointAnnotationType.TYPE_ID);
         ISEIterator iterator = new SEBreadthFirstIterator(this);
         while (iterator.hasNext()) {
            ISEDebugElement next = iterator.next();
            if (next instanceof ISENode) {
               ISENode node = (ISENode)next;
               boolean hit = breakpoint.isEnabled() && checkBreakpointHit(breakpoint, node);
               if (hit) {
                  ISEAnnotationLink[] links = node.getAnnotationLinks(breakpointType);
                  boolean found = false;
                  for (ISEAnnotationLink link : links) {
                     if (breakpointType.isBreakpointLink(link, breakpoint)) {
                        found = true;
                        ((BreakpointAnnotationLink)link).updateBreakpointName();
                     }
                  }
                  if (!found) {
                     ISEAnnotation[] annotations = getRegisteredAnnotations(breakpointType);
                     for (ISEAnnotation annotation : annotations) {
                        breakpointType.addBreakpointLink(node, annotation, breakpoint);
                     }
                  }
               }
               else {
                  // Remove may available links of the given breakpoint
                  ISEAnnotationLink[] links = node.getAnnotationLinks(breakpointType);
                  for (ISEAnnotationLink link : links) {
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
   public IBreakpoint[] computeHitBreakpoints(ISENode node) throws DebugException {
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
    * Checks if the given {@link IBreakpoint} is fulfilled in the given {@link ISENode}.
    * @param breakpoint The {@link IBreakpoint} to check.
    * @param node the {@link ISENode} to check.
    * @return {@code true} hit, {@code false} not hit.
    */
   protected abstract boolean checkBreakpointHit(IBreakpoint breakpoint, ISENode node);

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
   public void registerAnnotation(ISEAnnotation annotation) {
      if (annotation != null && !registeredAnnotations.contains(annotation)) {
         if (registeredAnnotations.add(annotation)) {
            fireAnnotationRegistered(new SEAnnotationEvent(this, annotation));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void unregisterAnnotation(ISEAnnotation annotation) {
      if (annotation != null) {
         if (registeredAnnotations.remove(annotation)) {
            ISEAnnotationLink[] links = annotation.getLinks();
            for (ISEAnnotationLink link : links) {
               link.getTarget().removeAnnotationLink(link);
            }
            fireAnnotationUnregistered(new SEAnnotationEvent(this, annotation));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotation[] getRegisteredAnnotations() {
      return registeredAnnotations.toArray(new ISEAnnotation[registeredAnnotations.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEAnnotation[] getRegisteredAnnotations(ISEAnnotationType type) {
      List<ISEAnnotation> result = new LinkedList<ISEAnnotation>();
      for (ISEAnnotation annotation : registeredAnnotations) {
         if (ObjectUtil.equals(type, annotation.getType())) {
            result.add(annotation);
         }
      }
      return result.toArray(new ISEAnnotation[result.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isRegistered(ISEAnnotation annotation) {
      return annotation != null && registeredAnnotations.contains(annotation);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void moveRegisteredAnnotation(ISEAnnotation annotation, int newIndex) {
      if (annotation != null && newIndex >= 0 && newIndex < registeredAnnotations.size()) {
         if (registeredAnnotations.remove(annotation)) {
            registeredAnnotations.add(newIndex, annotation);
            fireAnnotationMoved(new SEAnnotationEvent(this, annotation));
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int indexOfRegisteredAnnotation(ISEAnnotation annotation) {
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
   public void addAnnotationListener(ISEAnnotationListener l) {
      if (l != null) {
         annotationListener.add(l);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeAnnotationListener(ISEAnnotationListener l) {
      if (l != null) {
         annotationListener.remove(l);
      }
   }
   
   /**
    * Fires the event {@link ISEAnnotationListener#annotationRegistered(SEAnnotationEvent)}.
    * @param e The {@link SEAnnotationEvent}.
    */
   protected void fireAnnotationRegistered(SEAnnotationEvent e) {
      ISEAnnotationListener[] listener = annotationListener.toArray(new ISEAnnotationListener[annotationListener.size()]);
      for (ISEAnnotationListener l : listener) {
         l.annotationRegistered(e);
      }
   }
   
   /**
    * Fires the event {@link ISEAnnotationListener#annotationUnregistered(SEAnnotationEvent)}.
    * @param e The {@link SEAnnotationEvent}.
    */
   protected void fireAnnotationUnregistered(SEAnnotationEvent e) {
      ISEAnnotationListener[] listener = annotationListener.toArray(new ISEAnnotationListener[annotationListener.size()]);
      for (ISEAnnotationListener l : listener) {
         l.annotationUnregistered(e);
      }
   }
   
   /**
    * Fires the event {@link ISEAnnotationListener#annotationMoved(SEAnnotationEvent)}.
    * @param e The {@link SEAnnotationEvent}.
    */
   protected void fireAnnotationMoved(SEAnnotationEvent e) {
      ISEAnnotationListener[] listener = annotationListener.toArray(new ISEAnnotationListener[annotationListener.size()]);
      for (ISEAnnotationListener l : listener) {
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
      ISEIterator iter = new SEPreorderIterator(this);
      while (iter.hasNext()) {
         SWTUtil.checkCanceled(monitor);
         ISEDebugElement next = iter.next();
         if (next instanceof ISENode) {
            ISENode node = (ISENode)next;
            nodeCount++;
            ISENode[] children = node.getChildren();
            if (children.length == 0) {
               if (node instanceof ISETermination) {
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
   public SEMemorySourceModel getSourceModel() {
      return sourceModel;
   }
   
   /**
    * This method has to be called once for each {@link ISENode}
    * to add it to the {@link ISESourceModel}.
    * @param node The new {@link ISENode} to add to the {@link ISESourceModel}.
    * @throws DebugException Occurred Exception.
    */
   protected void addToSourceModel(ISENode node) throws DebugException {
      if (sourceModel != null && 
          node instanceof IStackFrame && getLaunch() != null) {
         IStackFrame stackFrame = (IStackFrame) node;
         ISourceLocator locator = getLaunch().getSourceLocator();
         if (locator != null) {
            Object source = locator.getSourceElement(stackFrame);
            if (source != null) {
               int lineNumber = stackFrame.getLineNumber();
               int charStart = stackFrame.getCharStart();
               int charEnd = stackFrame.getCharEnd();
               addToSourceModel(node, source, lineNumber, charStart, charEnd);
            }
         }
      }
   }
   
   /**
    * This method has to be called to register a specific range in the {@link ISESourceModel}.
    * @param node The {@link ISENode} to register.
    * @param source The source.
    * @param lineNumber The line number.
    * @param charStart The start character.
    * @param charEnd The end character.
    */
   protected void addToSourceModel(ISENode node, Object source, int lineNumber, int charStart, int charEnd) {
      if (sourceModel != null && node != null && source != null) {
         SEMemorySourceSummary summary = sourceModel.getSourceSummary(source);
         if (summary == null) {
            summary = new SEMemorySourceSummary(source);
            sourceModel.addSourceSummary(summary);
         }
         SEMemorySourceRange range = summary.getSourceRange(lineNumber, charStart, charEnd);
         if (range == null) {
            range = new SEMemorySourceRange(lineNumber, charStart, charEnd);
            summary.addSourceRange(range);
         }
         range.addDebugNode(node);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISESlicer getSlicer(ISENode seedNode, IVariable seedVariable, final String name) {
      return ArrayUtil.search(getSlicer(seedNode, seedVariable), new IFilter<ISESlicer>() {
         @Override
         public boolean select(ISESlicer element) {
            return ObjectUtil.equals(name, element.getName());
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISESlicer[] getSlicer(ISENode seedNode, IVariable seedVariable) {
      return null; // Slicing is not supported by default.
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