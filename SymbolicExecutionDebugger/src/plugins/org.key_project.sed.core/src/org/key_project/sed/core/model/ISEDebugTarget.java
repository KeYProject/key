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

package org.key_project.sed.core.model;

import java.util.Map;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.ITerminate;
import org.eclipse.debug.core.model.IThread;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.model.event.ISEAnnotationListener;
import org.key_project.sed.core.model.impl.AbstractSEDebugTarget;
import org.key_project.sed.core.model.memory.SEMemoryDebugTarget;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.sed.core.sourcesummary.ISESourceModel;

/**
 * A debug target is a symbolic debuggable execution context. For example, a debug target
 * may represent a symbolically debuggable method. A debug target is the root
 * of the debug element hierarchy. A debug target contains threads which are the
 * root of the symbolic execution tree. Minimally, a debug
 * target supports the following:
 * <ul>
 * <li>terminate ({@link ITerminate})</li>
 * </ul>
 * <p>
 * Generally, launching a debug session results in the creation of a
 * debug target. Launching is a client responsibility, as is debug target
 * creation.
 * </p>
 * <p>
 * A symbolic debug target is also a normal debug target ({@link IDebugTarget})
 * for compatibility reasons with the Eclipse debug API. But the default
 * provided {@link IThread}s are not used anymore. Instead the contained
 * {@link ISEThread}s are used.
 * </p>
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDebugTarget} instead of implementing this
 * interface directly. {@link SEMemoryDebugTarget} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ITerminate
 * @see AbstractSEDebugTarget
 */
public interface ISEDebugTarget extends ISEDebugElement, IDebugTarget {
   /**
    * Returns the name of this debug target. Name format is debug model
    * specific, and should be specified by a debug model.
    *
    * @return this target's name
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the debug target.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li></ul>
    */
   public String getName() throws DebugException;
   
   /**
    * Returns the threads contained in this debug target. An
    * empty collection is returned if this debug target contains
    * no threads.
    * 
    * @return a collection of threads
    * @exception DebugException if this method fails.  Reasons include:
    * <ul><li>Failure communicating with the debug target.  The DebugException's
    * status code contains the underlying exception responsible for
    * the failure.</li></ul>
    */   
   public ISEThread[] getSymbolicThreads() throws DebugException;
   
   /**
    * Registers the given {@link ISEAnnotation} to be used by {@link ISENode}s of this target.
    * @param annotation The {@link ISEAnnotation} to register.
    */
   public void registerAnnotation(ISEAnnotation annotation);
   
   /**
    * Unregisters the given {@link ISEAnnotation} not to be used anymore by {@link ISENode}s of this target.
    * @param annotation The {@link ISEAnnotation} to unregister.
    */
   public void unregisterAnnotation(ISEAnnotation annotation);
   
   /**
    * Moves the given {@link ISEAnnotation} to the given index.
    * @param annotation The {@link ISEAnnotation} to move.
    * @param newIndex The new index.
    */
   public void moveRegisteredAnnotation(ISEAnnotation annotation, int newIndex);
   
   /**
    * Returns the index of the given {@link ISEAnnotation}.
    * @param annotation The {@link ISEAnnotation} to get its index.
    * @return The index of the given {@link ISEAnnotation} or {@code -1} if not available.
    */
   public int indexOfRegisteredAnnotation(ISEAnnotation annotation);
   
   /**
    * Returns the number of registered {@link ISEAnnotation}.
    * @return The number of registered {@link ISEAnnotation}.
    */
   public int countRegisteredAnnotations();
   
   /**
    * Returns all registered {@link ISEAnnotation}s.
    * @return All registered {@link ISEAnnotation}s.
    */
   public ISEAnnotation[] getRegisteredAnnotations();
   
   /**
    * Returns all registered {@link ISEAnnotation}s of the given {@link ISEAnnotationType}.
    * @param type The {@link ISEAnnotationType}.
    * @return All registered {@link ISEAnnotation}s of the given {@link ISEAnnotationType}
    */
   public ISEAnnotation[] getRegisteredAnnotations(ISEAnnotationType type);
   
   /**
    * Checks if the given {@link ISEAnnotation} is registered.
    * @param annotation The {@link ISEAnnotation} to check.
    * @return {@code true} the {@link ISEAnnotation} is registered, {@code false} the {@link ISEAnnotation} is not registered.
    */
   public boolean isRegistered(ISEAnnotation annotation);
   
   /**
    * Adds the given {@link ISEAnnotationListener}.
    * @param l The {@link ISEAnnotationListener} to add.
    */
   public void addAnnotationListener(ISEAnnotationListener l);
   
   /**
    * Removes the given {@link ISEAnnotationListener}.
    * @param l The {@link ISEAnnotationListener} to remove.
    */
   public void removeAnnotationListener(ISEAnnotationListener l);
   
   /**
    * Computes some statistics of this {@link ISEDebugTarget}.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The computed statistics.
    * @throws DebugException Occurred Exception.
    */
   public Map<String, String> computeStatistics(IProgressMonitor monitor) throws DebugException;
   
   /**
    * Returns all currently used {@link IBreakpoint}s.
    * @return The currently used {@link IBreakpoint}s.
    */
   public IBreakpoint[] getBreakpoints();
   
   /**
    * Returns all {@link IBreakpoint}s which are fulfilled in the given {@link ISENode}.
    * @param node The {@link ISENode} to check.
    * @return The fulfilled {@link IBreakpoint}s in the given {@link ISENode}.
    */
   public IBreakpoint[] computeHitBreakpoints(ISENode node) throws DebugException;
   
   /**
    * Returns the {@link ISESourceModel} which manages the visited source parts
    * @return The {@link ISESourceModel} or {@code null} if not available.
    */
   public ISESourceModel getSourceModel();
   
   /**
    * Returns the available {@link ISESlicer} for the seed {@link ISENode}
    * and seed {@link IVariable}.
    * @param seedNode The seed {@link ISENode}.
    * @param seedVariable The seed {@link IVariable}.
    * @return The available {@link ISESlicer}.
    */
   public ISESlicer[] getSlicer(ISENode seedNode, IVariable seedVariable);
   
   /**
    * Returns the {@link ISESlicer} for the seed {@link ISENode}
    * and seed {@link IVariable} with the given name.
    * @param seedNode The seed {@link ISENode}.
    * @param seedVariable The seed {@link IVariable}.
    * @param name The name of the {@link ISESlicer} to search.
    * @return The {@link ISESlicer} with the given name or {@code null} if not available.
    */
   public ISESlicer getSlicer(ISENode seedNode, IVariable seedVariable, String name);

   /**
    * Checks if {@link ISEGroupable}s are supported or not.
    * @return {@code false} {@link ISEGroupable} are never contained in the symbolic execution tree, {@code true} {@link ISEGroupable} might be part of the symbolic execution tree.
    */
   public boolean isGroupingSupported();
}