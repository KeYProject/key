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

package de.hentschel.visualdbc.key.ui.editor;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IPersistableElement;

import de.hentschel.visualdbc.dbcmodel.DbcModel;

/**
 * An {@link IEditorInput} which defines a {@link DbcModel}.
 * @author Martin Hentschel
 */
public class DbcModelEditorInput extends PlatformObject implements IEditorInput{
   /**
    * The {@link DbcModel} to edit.
    */
   private DbcModel model;
   
   /**
    * Constructor.
    * @param model The {@link DbcModel} to edit.
    */
   public DbcModelEditorInput(DbcModel model) {
      Assert.isNotNull(model);
      this.model = model;
   }

   /**
    * Returns The {@link DbcModel} to edit.
    * @return The {@link DbcModel} to edit.
    */
   public DbcModel getModel() {
      return model;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean exists() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ImageDescriptor getImageDescriptor() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IPersistableElement getPersistable() {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getToolTipText() {
      return null;
   }
}