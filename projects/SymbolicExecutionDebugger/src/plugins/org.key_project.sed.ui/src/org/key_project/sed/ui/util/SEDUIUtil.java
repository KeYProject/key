/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

package org.key_project.sed.ui.util;

import java.util.Deque;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.viewers.IContentProvider;
import org.eclipse.jface.viewers.ILazyTreeContentProvider;
import org.eclipse.jface.viewers.ILazyTreePathContentProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.TreePath;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Widget;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.provider.SEDDebugNodeContentProvider;
import org.key_project.sed.core.provider.SEDDebugTargetContentProvider;
import org.key_project.util.eclipse.JobUtil;
import org.key_project.util.eclipse.job.AbstractWorkbenchPartJob;
import org.key_project.util.eclipse.job.ScheduledJobCollector;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithResult;

/**
 * Provides static methods which makes working with the Eclipse Debug UI and 
 * SED UI easier.
 * @author Martin Hentschel
 */
public final class SEDUIUtil {
   /**
    * Forbid instances.
    */
   private SEDUIUtil() {
   }

   /**
    * Selects the given elements in the given {@link IDebugView}.
    * @param parentPart The current {@link IWorkbenchPart} which requests the selection change.
    * @param debugView The {@link IDebugView} to change selection in.
    * @param selection The new selection to set in the {@link IDebugView}.
    */
   public static void selectInDebugView(IWorkbenchPart parentPart, 
                                        final IDebugView debugView, 
                                        ISelection selection) {
      selectInDebugView(parentPart, debugView, SWTUtil.toList(selection));
   }

   /**
    * Selects the given elements in the given {@link IDebugView}.
    * @param parentPart The current {@link IWorkbenchPart} which requests the selection change.
    * @param debugView The {@link IDebugView} to change selection in.
    * @param selection The new selection to set in the {@link IDebugView}.
    */
   public static void selectInDebugView(IWorkbenchPart parentPart, 
                                        final IDebugView debugView, 
                                        final List<?> selection) {
      // Make sure that the old selected business objects are different to the new one
      ISelection oldSelection = debugView.getViewer().getSelection();
      if (!selection.equals(SWTUtil.toList(oldSelection))) {
         // Change selection in debug view if new elements are selected in a Job because the debug view uses Jobs itself to expand the debug model and it is required to wait for them.
         AbstractWorkbenchPartJob.cancelJobs(parentPart);
         Job selectJob = new AbstractWorkbenchPartJob("Synchronizing selection", parentPart) {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
               try {
                  // Expand viewer up to the elements to select.
                  final Viewer debugViewer = debugView.getViewer();
                  if (debugViewer instanceof TreeViewer) {
                     TreeViewer treeViewer = (TreeViewer)debugViewer;
                     for (Object element : selection) {
                        try {
                           monitor.beginTask(getName(), IProgressMonitor.UNKNOWN);
                           monitor.subTask("Collecting unknown elements");
                           Deque<Object> expandQue = collectUnknownElementsInParentHierarchy(treeViewer, element);
                           monitor.beginTask(getName(), expandQue.size() + 1);
                           monitor.subTask("Expanding unknown elements");
                           injectElements(treeViewer, expandQue, monitor);
                        }
                        catch (DebugException e) {
                           LogUtil.getLogger().logError("Can't expand debug view to element \"" + element + "\".", e);
                        }
                     }
                  }
                  // Select new elements
                  monitor.subTask("Select element");
                  ISelection newSelection = SWTUtil.createSelection(selection);
                  SWTUtil.select(debugViewer, newSelection, true);
                  monitor.worked(1);
                  monitor.done();
                  return Status.OK_STATUS;
               }
               catch (OperationCanceledException e) {
                  return Status.CANCEL_STATUS;
               }
            }
         };
         selectJob.schedule();
      }
   }

   /**
    * <p>
    * Collects all elements in the parent hierarchy starting from the given one
    * which are unknown in the given {@link TreeViewer}.
    * </p>
    * <p>
    * Unknown elements are possible if an {@link ILazyTreeContentProvider} or
    * an {@link ILazyTreePathContentProvider} is used.
    * </p>
    * @param treeViewer The {@link TreeViewer} to search in.
    * @param element The element to start search for unknown elements.
    * @return A {@link Deque} which contains all unknown elements in order from root to given element.
    * @throws DebugException Occurred Exception.
    */
   protected static Deque<Object> collectUnknownElementsInParentHierarchy(final TreeViewer treeViewer, Object element) throws DebugException {
      Deque<Object> expandQue = new LinkedList<Object>();
      while (element != null) {
         // Check if the element is unknown in tree
         final Object toTest = element;
         IRunnableWithResult<Boolean> run = new AbstractRunnableWithResult<Boolean>() {
            @Override
            public void run() {
               Widget item = treeViewer.testFindItem(toTest);
               setResult(item == null);
            }
         };
         treeViewer.getControl().getDisplay().syncExec(run);
         if (run.getResult() != null && run.getResult().booleanValue()) {
            // Element is not known, add to deque and continue with parent.
            expandQue.addFirst(element);
            // Update current element for next loop iteration.
            element = getParent(element);
         }
         else {
            // Element is known in tree, search can be stopped.
            element = null;
         }
      }
      return expandQue;
   }
   
   /**
    * Computes the parent of the given element, because the used
    * {@link ILazyTreePathContentProvider} implementation
    * of the debug viewer returns {@code null} via
    * {@link ILazyTreePathContentProvider#getParents(Object)}.
    * @param element The current element.
    * @return The parent element if available or {@code null} otherwise.
    * @throws DebugException Occurred Exception.
    */
   protected static Object getParent(Object element) throws DebugException {
      if (element instanceof ISEDDebugNode) {
         return SEDDebugNodeContentProvider.getDefaultInstance().getDebugNodeParent(element);
      }
      else if (element instanceof ISEDDebugTarget) {
         return SEDDebugTargetContentProvider.getDefaultInstance().getParent(element);
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the children of the given {@link Object} shown in
    * the viewer of view "Debug".
    * @param element The element to get children for.
    * @return The available children.
    * @throws DebugException Occurred Exception.
    */
   protected static Object[] getChildren(Object element) throws DebugException {
      if (element instanceof ISEDDebugTarget) {
         return SEDDebugTargetContentProvider.getDefaultInstance().getAllChildren(element);
      }
      else if (element instanceof ISEDDebugNode) {
         return SEDDebugNodeContentProvider.getDefaultInstance().getAllDebugNodeChildren(element);
      }
      else {
         return null;
      }
   }

   /**
    * Injects all unknown elements of the {@link TreeViewer} in the
    * parent hierarchy order defined by the given {@link Deque}.
    * @param treeViewer The {@link TreeViewer} to make elements known in.
    * @param injectQue The {@link Deque} which contains the unknown elements from parent to leaf.
    * @param monitor The {@link IProgressMonitor} to use.
    * @throws DebugException Occurred Exception
    */
   protected static void injectElements(final TreeViewer treeViewer, 
                                        Deque<Object> injectQue,
                                        final IProgressMonitor monitor) throws DebugException {
      // Check if something must be done
      if (!CollectionUtil.isEmpty(injectQue)) {
         // Check if the provider is of the expected form.
         IContentProvider cp = treeViewer.getContentProvider();
         if (cp instanceof ILazyTreePathContentProvider) {
            final ILazyTreePathContentProvider lazyContentProvider = (ILazyTreePathContentProvider)cp;
            // Create tree path to last known element
            final LinkedList<Object> tpElements = new LinkedList<Object>();
            Object knownParent = getParent(injectQue.getFirst());
            while (knownParent != null) {
               SWTUtil.checkCanceled(monitor);
               tpElements.addFirst(knownParent);
               knownParent = getParent(knownParent);
            }
            // Injects elements starting at the root to make them familiar in tree
            for (final Object toInject : injectQue) {
               SWTUtil.checkCanceled(monitor);
               // Compute index on parent
               Object parent = getParent(toInject);
               final int viewIndex = ArrayUtil.indexOf(getChildren(parent), toInject);
               // Create tree path to current element
               final TreePath tp = new TreePath(tpElements.toArray());
               // Create job collector to collect update jobs started by the Debug API
               IFilter<Job> jobFilter = new IFilter<Job>() {
                  @Override
                  public boolean select(Job element) {
                     String className = element.getClass().getName();
                     return className.startsWith("org.eclipse.debug") ||
                            className.startsWith("org.eclipse.ui.internal.progress");
                  }
               };
               ScheduledJobCollector collector = new ScheduledJobCollector(jobFilter);
               try {
                  // Start collecting update jobs started by the debug view
                  collector.start();
                  IRunnableWithException run = new AbstractRunnableWithException() {
                     @Override
                     public void run() {
                        try {
                           // Inject the element into the TreeViewer
                           lazyContentProvider.updateChildCount(tp, 0);
                           lazyContentProvider.updateElement(tp, viewIndex);
                        }
                        catch (Exception e) {
                           setException(e);
                        }
                     }
                  };
                  treeViewer.getControl().getDisplay().syncExec(run);
                  if (run.getException() != null) {
                     throw new DebugException(LogUtil.getLogger().createErrorStatus(run.getException().getMessage(), run.getException()));
                  }
               }
               finally {
                  // Stop collecting update jobs
                  collector.stop();
               }
               // Wait until all update jobs have finished before
               Job[] jobs = collector.getJobs();
               for (Job job : jobs) {
                  SWTUtil.checkCanceled(monitor);
                  JobUtil.waitFor(job, 10);
               }         
               // Update tree path for next loop iteration
               tpElements.add(toInject);
               // Update monitor
               monitor.worked(1);
            }
         }
      }
   }
}