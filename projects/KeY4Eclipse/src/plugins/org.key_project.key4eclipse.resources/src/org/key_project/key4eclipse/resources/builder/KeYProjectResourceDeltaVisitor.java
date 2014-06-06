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

package org.key_project.key4eclipse.resources.builder;

import java.util.LinkedList;

import org.eclipse.core.resources.IResourceDelta;
import org.eclipse.core.resources.IResourceDeltaVisitor;
import org.eclipse.core.runtime.CoreException;

/**
 * DeltaVisitor to visit every child of the given delta.
 * @author Stefan Käsdorf
 */
public class KeYProjectResourceDeltaVisitor implements IResourceDeltaVisitor{

   
   private LinkedList<IResourceDelta> deltas;
   public KeYProjectResourceDeltaVisitor() throws CoreException{
      this.deltas = new LinkedList<IResourceDelta>();
   }
   
   
   public LinkedList<IResourceDelta> getDeltaList(){
      return this.deltas;
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean visit(IResourceDelta delta) throws CoreException {
      deltas.add(delta);
      return true;
   }
   
   

}