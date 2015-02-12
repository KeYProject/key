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

package org.key_project.util.eclipse.swt.view;

import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.ViewPart;

/**
 * Extension of {@link ViewPart} which uses another {@link IWorkbenchPart}
 * to compute the shown content.
 * @author Martin Hentschel
 */
public abstract class AbstractWorkbenchPartBasedView extends ViewPart {
   /**
    * Listens for changes on the {@link IWorkbenchPage} of this {@link IViewSite}.
    */
   private IPartListener partListener = new IPartListener() {
      @Override
      public void partOpened(IWorkbenchPart part) {
         handlePartOpened(part);
      }
      
      @Override
      public void partDeactivated(IWorkbenchPart part) {
         handlePartDeactivated(part);
      }
      
      @Override
      public void partClosed(IWorkbenchPart part) {
         handlePartClosed(part);
      }
      
      @Override
      public void partBroughtToTop(IWorkbenchPart part) {
         handlePartBroughtToTop(part);
      }
      
      @Override
      public void partActivated(IWorkbenchPart part) {
         handlePartActivated(part);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IViewSite site) throws PartInitException {
      super.init(site);
      getViewSite().getPage().addPartListener(partListener);
   }

   /**
    * Handles the event {@link IPartListener#partClosed(IWorkbenchPart)}.
    * @param part The closed {@link IWorkbenchPart}.
    */
   protected void handlePartClosed(IWorkbenchPart part) {
   }

   /**
    * Handles the event {@link IPartListener#partOpened(IWorkbenchPart)}.
    * @param part The opened {@link IWorkbenchPart}.
    */
   protected void handlePartOpened(IWorkbenchPart part) {
   }

   /**
    * Handles the event {@link IPartListener#partActivated(IWorkbenchPart)}.
    * @param part The activated {@link IWorkbenchPart}.
    */
   protected void handlePartActivated(IWorkbenchPart part) {
   }

   /**
    * Handles the event {@link IPartListener#partBroughtToTop(IWorkbenchPart)}.
    * @param part The {@link IWorkbenchPart} brought to top.
    */
   protected void handlePartBroughtToTop(IWorkbenchPart part) {
   }

   /**
    * Handles the event {@link IPartListener#partDeactivated(IWorkbenchPart)}.
    * @param part The deactivated {@link IWorkbenchPart}.
    */
   protected void handlePartDeactivated(IWorkbenchPart part) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      getViewSite().getPage().removePartListener(partListener);
      super.dispose();
   }
}