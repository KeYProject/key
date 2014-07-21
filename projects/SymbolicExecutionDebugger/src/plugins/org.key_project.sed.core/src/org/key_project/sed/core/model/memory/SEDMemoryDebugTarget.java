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

package org.key_project.sed.core.model.memory;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.debug.core.model.IDebugTarget;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.model.impl.AbstractSEDDebugTarget;

/**
 * Implementation of {@link ISEDDebugTarget} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEDMemoryDebugTarget extends AbstractSEDDebugTarget implements ISEDMemoryDebugTarget {
   /**
    * The contained {@link ISEDThread}s.
    */
   private final List<ISEDThread> threads = new LinkedList<ISEDThread>();
   
   /**
    * Constructor.
    * @param launch The {@link ILaunch} in that this {@link IDebugTarget} is used.
    * @param executable {@code true} Support suspend, resume, etc.; {@code false} Do not support suspend, resume, etc.
    */
   public SEDMemoryDebugTarget(ILaunch launch, boolean executable) {
      super(launch, executable);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDThread[] getSymbolicThreads() throws DebugException {
      return threads.toArray(new ISEDThread[0]);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void addSymbolicThread(ISEDThread thread) {
      if (thread != null) {
         threads.add(thread);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addSymbolicThread(int index, ISEDThread thread) {
      if (thread != null) {
         threads.add(index, thread);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removeSymbolicThread(ISEDThread thread) {
      if (thread != null) {
         threads.remove(thread);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int indexOfSymbolicThread(ISEDThread thread) {
      if (thread != null) {
         return threads.indexOf(thread);
      }
      else {
         return -1;
      }
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setModelIdentifier(String modelIdentifier) {
      super.setModelIdentifier(modelIdentifier);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setName(String name) {
      super.setName(name);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Changed visibility to public.
    * </p>
    */
   @Override
   public void setId(String id) {
      super.setId(id);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void initBreakpoint(IBreakpoint breakpoint) throws DebugException {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IBreakpoint[] getBreakpoints() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean checkBreakpointHit(IBreakpoint breakpoint, ISEDDebugNode node) {
      return false;
   }
}