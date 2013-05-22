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

package de.hentschel.visualdbc.dbcmodel.diagram.providers;

import java.lang.ref.WeakReference;

import org.eclipse.gef.EditPart;
import org.eclipse.gef.EditPartFactory;
import org.eclipse.gmf.runtime.common.core.service.IOperation;
import org.eclipse.gmf.runtime.diagram.ui.editparts.IGraphicalEditPart;
import org.eclipse.gmf.runtime.diagram.ui.services.editpart.AbstractEditPartProvider;
import org.eclipse.gmf.runtime.diagram.ui.services.editpart.CreateGraphicEditPartOperation;
import org.eclipse.gmf.runtime.diagram.ui.services.editpart.IEditPartOperation;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbCEditPartFactory;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcModelEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCVisualIDRegistry;

/**
 * @generated
 */
public class DbCEditPartProvider extends AbstractEditPartProvider {

   /**
    * @generated
    */
   private EditPartFactory factory;

   /**
    * @generated
    */
   private boolean allowCaching;

   /**
    * @generated
    */
   private WeakReference cachedPart;

   /**
    * @generated
    */
   private WeakReference cachedView;

   /**
    * @generated
    */
   public DbCEditPartProvider() {
      setFactory(new DbCEditPartFactory());
      setAllowCaching(true);
   }

   /**
    * @generated
    */
   public final EditPartFactory getFactory() {
      return factory;
   }

   /**
    * @generated
    */
   protected void setFactory(EditPartFactory factory) {
      this.factory = factory;
   }

   /**
    * @generated
    */
   public final boolean isAllowCaching() {
      return allowCaching;
   }

   /**
    * @generated
    */
   protected synchronized void setAllowCaching(boolean allowCaching) {
      this.allowCaching = allowCaching;
      if (!allowCaching) {
         cachedPart = null;
         cachedView = null;
      }
   }

   /**
    * @generated
    */
   protected IGraphicalEditPart createEditPart(View view) {
      EditPart part = factory.createEditPart(null, view);
      if (part instanceof IGraphicalEditPart) {
         return (IGraphicalEditPart) part;
      }
      return null;
   }

   /**
    * @generated
    */
   protected IGraphicalEditPart getCachedPart(View view) {
      if (cachedView != null && cachedView.get() == view) {
         return (IGraphicalEditPart) cachedPart.get();
      }
      return null;
   }

   /**
    * @generated
    */
   public synchronized IGraphicalEditPart createGraphicEditPart(View view) {
      if (isAllowCaching()) {
         IGraphicalEditPart part = getCachedPart(view);
         cachedPart = null;
         cachedView = null;
         if (part != null) {
            return part;
         }
      }
      return createEditPart(view);
   }

   /**
    * @generated
    */
   public synchronized boolean provides(IOperation operation) {
      if (operation instanceof CreateGraphicEditPartOperation) {
         View view = ((IEditPartOperation) operation).getView();
         if (!DbcModelEditPart.MODEL_ID.equals(DbCVisualIDRegistry
               .getModelID(view))) {
            return false;
         }
         if (isAllowCaching() && getCachedPart(view) != null) {
            return true;
         }
         IGraphicalEditPart part = createEditPart(view);
         if (part != null) {
            if (isAllowCaching()) {
               cachedPart = new WeakReference(part);
               cachedView = new WeakReference(view);
            }
            return true;
         }
      }
      return false;
   }
}