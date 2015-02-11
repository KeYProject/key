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

package org.key_project.keyide.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.key_project.keyide.ui.providers.BranchFolder;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;

/**
 * This {@link PropertyTester} checks if the currently selected {@link Node} is a {@link Goal}.
 * @author Martin Hentschel
 */
public class GoalPropertyTester extends PropertyTester {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(Object receiver, String property, Object[] args, Object expectedValue) {
      if (receiver instanceof IStructuredSelection){
         IStructuredSelection selection = (IStructuredSelection)receiver;
         Object element = selection.getFirstElement();
         Node node = null;
         if (element instanceof Node){
            node = (Node)element;
         }
         else if (element instanceof BranchFolder){
            node = ((BranchFolder)element).getChild();
         }
         return node != null && !node.isClosed() && node.childrenCount() == 0;
      }
      else {
         return false;
      }
   }
}