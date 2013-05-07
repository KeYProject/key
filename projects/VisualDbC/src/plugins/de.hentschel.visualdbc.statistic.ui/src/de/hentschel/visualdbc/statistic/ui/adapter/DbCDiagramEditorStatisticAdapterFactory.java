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

package de.hentschel.visualdbc.statistic.ui.adapter;

import org.eclipse.jface.viewers.ISelection;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.statistic.ui.control.IStatisticProvider;
import de.hentschel.visualdbc.statistic.ui.util.StatisticUtil;
import de.hentschel.visualdbc.statistic.ui.view.DbcStatisticViewPart;
import de.hentschel.visualdbc.statistic.ui.view.IStatisticViewPart;

/**
 * Converts a given {@link DbCDiagramEditor} into an {@link IStatisticViewPart}.
 * @author Martin Hentschel
 */
public class DbCDiagramEditorStatisticAdapterFactory extends AbstractStatisticAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object getAdapter(final Object adaptableObject, @SuppressWarnings("rawtypes") Class adapterType) {
      final IStatisticProvider provider = new IStatisticProvider() {
         private DbCDiagramEditor editor;
         
         @Override
         public DbcModel getModel() {
            if (adaptableObject instanceof DbCDiagramEditor) {
               editor = (DbCDiagramEditor)adaptableObject;
               return (DbcModel)editor.getDiagram().getElement();
            }
            else {
               return null;
            }
         }

         @Override
         public void select(ISelection selection) {
            StatisticUtil.select(editor, selection);
         }
      };
      return new DbcStatisticViewPart(provider);
   }
}