/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package de.hentschel.visualdbc.statistic.ui.adapter;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.statistic.ui.control.IStatisticProvider;
import de.hentschel.visualdbc.statistic.ui.view.DbcStatisticViewPart;

/**
 * Converts a given {@link DbCDiagramEditor} into an {@link IStatisticProvider}.
 * @author Martin Hentschel
 */
public class DbCDiagramEditorStatisticAdapterFactory extends AbstractStatisticAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object getAdapter(final Object adaptableObject, @SuppressWarnings("rawtypes") Class adapterType) {
      final IStatisticProvider provider = new IStatisticProvider() {
         @Override
         public DbcModel getModel() {
            if (adaptableObject instanceof DbCDiagramEditor) {
               DbCDiagramEditor editor = (DbCDiagramEditor)adaptableObject;
               return (DbcModel)editor.getDiagram().getElement();
            }
            else {
               return null;
            }
         }};
         return new DbcStatisticViewPart(provider);
   }
}
