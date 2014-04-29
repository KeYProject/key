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

package de.hentschel.visualdbc.key.ui.editor;

import org.eclipse.ui.IEditorInput;

import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;

/**
 * Extends the functionality of {@link DbCDiagramEditor} to support {@link DbcModelEditorInput}s.
 * @author Martin Hentschel
 */
public class DbCModelDiagramEditor extends DbCDiagramEditor {
   /**
    * Constructor.
    */
   public DbCModelDiagramEditor() {
      super();
   }

   /**
    * Constructor.
    * @param hasFlyoutPalette Show palette?
    */
   public DbCModelDiagramEditor(boolean hasFlyoutPalette) {
      super(hasFlyoutPalette);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void setDocumentProvider(IEditorInput input) {
      setDocumentProvider(new DbCModelDocumentProvider());
   }
}