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

package org.key_project.keyide.ui.views;

import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.part.IPage;
import org.eclipse.ui.part.IPageBookViewPage;
import org.eclipse.ui.part.MessagePage;
import org.eclipse.ui.part.PageBook;
import org.eclipse.ui.part.PageBookView;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.gui.configuration.StrategySettings;
import de.uka.ilkd.key.proof.Proof;

/**
 * <p>
 * This {@link PageBookView} shows {@link IStrategySettingsPage}s provided
 * by the active {@link IEditorPart} via {@link IEditorPart#getAdapter(Class)}.
 * </p>
 * <p>
 * The returned pages are used to edit {@link StrategySettings} of the
 * currently active {@link Proof}.
 * </p>
 * @author Martin Hentschel
 */
public class StrategySettingsView extends PageBookView {
   /**
    * The ID of this view.
    */
   public static final String VIEW_ID = "org.key_project.keyide.ui.view.StrategySettings";

   /**
    * {@inheritDoc}
    */
   @Override
   protected IPage createDefaultPage(PageBook book) {
      MessagePage page = new MessagePage();
      initPage(page);
      page.createControl(book);
      page.setMessage("Strategy Settings are not available");
      return page;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected PageRec doCreatePage(IWorkbenchPart part) {
      // Try to get an outline page.
      Object obj = part != null ? part.getAdapter(IStrategySettingsPage.class) : null;
      if (obj instanceof IStrategySettingsPage) {
         IStrategySettingsPage page = (IStrategySettingsPage) obj;
         if (page instanceof IPageBookViewPage) {
            initPage((IPageBookViewPage) page);
         }
         page.createControl(getPageBook());
         return new PageRec(part, page);
      }
      // There is no content outline
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void doDestroyPage(IWorkbenchPart part, PageRec pageRecord) {
      IStrategySettingsPage page = (IStrategySettingsPage) pageRecord.page;
      page.dispose();
      pageRecord.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IWorkbenchPart getBootstrapPart() {
      return WorkbenchUtil.getActiveEditor();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean isImportant(IWorkbenchPart part) {
      return part instanceof IEditorPart;
   }
}