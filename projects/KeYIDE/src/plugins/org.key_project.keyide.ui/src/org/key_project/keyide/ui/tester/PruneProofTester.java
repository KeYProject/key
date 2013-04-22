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

package org.key_project.keyide.ui.tester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.jface.viewers.TreeSelection;
import org.key_project.keyide.ui.providers.BranchFolder;

import de.uka.ilkd.key.proof.Node;

// TODO: Document class PruneProofTester
public class PruneProofTester extends PropertyTester {
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      if (receiver instanceof TreeSelection){
         TreeSelection selection = (TreeSelection)receiver;
         Object element = selection.getFirstElement();
         if (element instanceof Node){
            return !((Node)element).isClosed();
         }
         else if (element instanceof BranchFolder){
            return !((BranchFolder)element).isClosed();
         }
         else {
            return false;
         }
      }
      else {
         return false;
      }
   }
}