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

package org.key_project.sed.ui.visualization.util;

import org.eclipse.graphiti.features.context.IMultiDeleteInfo;
import org.eclipse.graphiti.features.context.impl.MultiDeleteInfo;

/**
 * Implementation of {@link IMultiDeleteInfo} as subclass of {@link MultiDeleteInfo}
 * which also allows to change the value of {@link #getNumber()} via
 * {@link #setNumber(int)}.
 * @author Martin Hentschel
 */
public class EditableMultiDeleteInfo extends MultiDeleteInfo {
   /**
    * The number of elements which are selected for deletion.
    */
   private int number;
   
   /**
    * 
    * @param showDialog
    * @param deleteCanceled
    */
   public EditableMultiDeleteInfo(boolean showDialog, boolean deleteCanceled) {
      this(showDialog, deleteCanceled, 1);
   }
   
   /**
    * 
    * @param showDialog Show or suppress dialog?
    * @param deleteCanceled Initial canceled state.
    * @param number The number of elements which are selected for deletion.
    */
   public EditableMultiDeleteInfo(boolean showDialog, boolean deleteCanceled, int number) {
      super(showDialog, deleteCanceled, number);
      this.number = number;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getNumber() {
      return number;
   }

   /**
    * Sets the number of elements which are selected for deletion.
    * @param number The number of elements which are selected for deletion.
    */
   public void setNumber(int number) {
      this.number = number;
   }
}