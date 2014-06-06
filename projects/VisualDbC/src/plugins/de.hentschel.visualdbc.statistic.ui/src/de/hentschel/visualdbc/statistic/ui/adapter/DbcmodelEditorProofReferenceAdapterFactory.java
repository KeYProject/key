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

package de.hentschel.visualdbc.statistic.ui.adapter;

import java.util.List;

import org.eclipse.ui.IEditorPart;

import de.hentschel.visualdbc.dbcmodel.presentation.DbcmodelEditor;
import de.hentschel.visualdbc.statistic.ui.control.IProofReferenceProvider;
import de.hentschel.visualdbc.statistic.ui.util.StatisticUtil;
import de.hentschel.visualdbc.statistic.ui.view.DbcProofReferencesViewPart;
import de.hentschel.visualdbc.statistic.ui.view.IProofReferencesViewPart;

/**
 * Converts a given {@link DbcmodelEditor} into an {@link IProofReferencesViewPart}.
 * @author Martin Hentschel
 */
public class DbcmodelEditorProofReferenceAdapterFactory extends AbstractProofReferenceAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Object adaptableObject, Class adapterType) {
      if (adaptableObject instanceof IEditorPart) {
         final DbcmodelEditor editor = adaptableObject instanceof DbcmodelEditor ? (DbcmodelEditor)adaptableObject : null;
         IProofReferenceProvider provider = new IProofReferenceProvider() {
            @Override
            public List<?> extractElementsToShow(List<?> elements) {
               return elements;
            }

            @Override
            public void select(List<?> toSelect) {
               StatisticUtil.select(editor, toSelect);
            }
         };
         return new DbcProofReferencesViewPart((IEditorPart)adaptableObject, provider);
      }
      else {
         return null;
      }
   }
}