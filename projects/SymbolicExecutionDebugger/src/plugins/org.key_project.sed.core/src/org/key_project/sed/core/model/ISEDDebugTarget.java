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

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.model.ITerminate;
import org.eclipse.debug.core.model.IThread;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.event.ISEDAnnotationListener;
import org.key_project.sed.core.model.impl.AbstractSEDDebugTarget;
import org.key_project.sed.core.model.memory.SEDMemoryDebugTarget;

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
 * {@link ISEDThread}s are used.
 * </p>
 * <p>
 * Clients may implement this interface. It is recommended to subclass
 * from {@link AbstractSEDDebugTarget} instead of implementing this
 * interface directly. {@link SEDMemoryDebugTarget} is also a default
 * implementation that stores all values in the memory.
 * </p>
 * @author Martin Hentschel
 * @see ITerminate
 * @see AbstractSEDDebugTarget
 */
public interface ISEDDebugTarget extends ISEDDebugElement, IDebugTarget {
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
   public ISEDThread[] getSymbolicThreads() throws DebugException;
   
   /**
    * Registers the given {@link ISEDAnnotation} to be used by {@link ISEDDebugNode}s of this target.
    * @param annotation The {@link ISEDAnnotation} to register.
    */
   public void registerAnnotation(ISEDAnnotation annotation);
   
   /**
    * Unregisters the given {@link ISEDAnnotation} not to be used anymore by {@link ISEDDebugNode}s of this target.
    * @param annotation The {@link ISEDAnnotation} to unregister.
    */
   public void unregisterAnnotation(ISEDAnnotation annotation);
   
   /**
    * Moves the given {@link ISEDAnnotation} to the given index.
    * @param annotation The {@link ISEDAnnotation} to move.
    * @param newIndex The new index.
    */
   public void moveRegisteredAnnotation(ISEDAnnotation annotation, int newIndex);
   
   /**
    * Returns the index of the given {@link ISEDAnnotation}.
    * @param annotation The {@link ISEDAnnotation} to get its index.
    * @return The index of the given {@link ISEDAnnotation} or {@code -1} if not available.
    */
   public int indexOfRegisteredAnnotation(ISEDAnnotation annotation);
   
   /**
    * Returns the number of registered {@link ISEDAnnotation}.
    * @return The number of registered {@link ISEDAnnotation}.
    */
   public int countRegisteredAnnotations();
   
   /**
    * Returns all registered {@link ISEDAnnotation}s.
    * @return All registered {@link ISEDAnnotation}s.
    */
   public ISEDAnnotation[] getRegisteredAnnotations();
   
   /**
    * Returns all registered {@link ISEDAnnotation}s of the given {@link ISEDAnnotationType}.
    * @param type The {@link ISEDAnnotationType}.
    * @return All registered {@link ISEDAnnotation}s of the given {@link ISEDAnnotationType}
    */
   public ISEDAnnotation[] getRegisteredAnnotations(ISEDAnnotationType type);
   
   /**
    * Checks if the given {@link ISEDAnnotation} is registered.
    * @param annotation The {@link ISEDAnnotation} to check.
    * @return {@code true} the {@link ISEDAnnotation} is registered, {@code false} the {@link ISEDAnnotation} is not registered.
    */
   public boolean isRegistered(ISEDAnnotation annotation);
   
   /**
    * Adds the given {@link ISEDAnnotationListener}.
    * @param l The {@link ISEDAnnotationListener} to add.
    */
   public void addAnnotationListener(ISEDAnnotationListener l);
   
   /**
    * Removes the given {@link ISEDAnnotationListener}.
    * @param l The {@link ISEDAnnotationListener} to remove.
    */
   public void removeAnnotationListener(ISEDAnnotationListener l);
}