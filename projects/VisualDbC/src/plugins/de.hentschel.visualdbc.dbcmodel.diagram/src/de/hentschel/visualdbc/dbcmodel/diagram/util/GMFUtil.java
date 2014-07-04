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

package de.hentschel.visualdbc.dbcmodel.diagram.util;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartViewer;
import org.eclipse.gmf.runtime.diagram.ui.editparts.ConnectionEditPart;
import org.eclipse.gmf.runtime.notation.View;

/**
 * Provides utility methods for GMF.
 * @author Martin Hentschel
 * @generated NOT
 */
public final class GMFUtil {
   /**
    * Forbid instances.
    */
   private GMFUtil() {
   }

   /**
    * Returns all {@link EditPart}s although if they are not contained in the 
    * containment hierarchy, like {@link ConnectionEditPart}s.
    * @param parent The parent that has a reference to the viewer.
    * @param toSearch The {@link EObject} for that the {@link EditPart} is needed.
    * @return The found {@link EditPart}s or {@code null} if no one were found.
    */
   public static Collection<EditPart> findEditParts(EditPart parent, EObject toSearch) {
      return findEditParts(parent.getViewer(), toSearch);
   }

   /**
    * Returns all {@link EditPart}s although if they are not contained in the 
    * containment hierarchy, like {@link ConnectionEditPart}s.
    * @param viewer The viewer to use.
    * @param toSearch The {@link EObject} for that the {@link EditPart} is needed.
    * @return The found {@link EditPart}s or {@code null} if no one were found.
    */
   public static Collection<EditPart> findEditParts(EditPartViewer viewer, EObject toSearch) {
      Map<?, ?> map = viewer.getEditPartRegistry();
      Collection<?> entries = map.values();
      Iterator<?> entryIter = entries.iterator();
      Collection<EditPart> result = new HashSet<EditPart>();
      while (entryIter.hasNext()) {
         Object entry = entryIter.next();
         Assert.isTrue(entry instanceof EditPart);
         EditPart editPart = (EditPart)entry;
         if (toSearch != null ? toSearch.equals(editPart.getAdapter(EObject.class)) : editPart.getAdapter(EObject.class) == null) {
            result.add(editPart);
         }
      }
      return result;
   }

   /**
    * Returns for each element its model element if it is an {@link EditPart}.
    * @param elements The elements which are maybe {@link EditPart}s.
    * @return The model elements.
    */
   public static List<?> getModelObjects(Collection<?> elements) {
      List<Object> result = new LinkedList<Object>();
      if (elements != null) {
         for (Object element : elements) {
            if (element instanceof EditPart) {
               result.add(getModelObject((EditPart)element));
            }
            else {
               result.add(element);
            }
         }
      }
      return result;
   }

   /**
    * Returns the model object represented by the given {@link EditPart}.
    * @param editPart The given {@link EditPart}.
    * @return The represented model object.
    */
   public static Object getModelObject(EditPart editPart) {
      Object model = editPart != null ? editPart.getModel() : null;
      if (model instanceof View) {
         return ((View)model).getElement();
      }
      else {
         return model;
      }
   }
}