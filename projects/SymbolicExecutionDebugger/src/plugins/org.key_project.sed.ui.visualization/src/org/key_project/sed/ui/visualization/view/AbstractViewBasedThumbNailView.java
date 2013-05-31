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

package org.key_project.sed.ui.visualization.view;

import org.eclipse.draw2d.Figure;
import org.eclipse.draw2d.LightweightSystem;
import org.eclipse.draw2d.MarginBorder;
import org.eclipse.draw2d.Viewport;
import org.eclipse.gef.GraphicalViewer;
import org.eclipse.gef.LayerConstants;
import org.eclipse.gef.editparts.LayerManager;
import org.eclipse.gef.editparts.SimpleRootEditPart;
import org.eclipse.graphiti.ui.internal.editor.ThumbNailView;
import org.eclipse.graphiti.ui.internal.fixed.FixedScrollableThumbnail;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Canvas;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;

/**
 * <p>
 * This {@link IViewPart} is used to show a thumbnail of a Graphiti editor
 * which is always provided from the same view (see {@link AbstractViewBasedView}).
 * </p>
 * <p>
 * The implementation was copied from {@link ThumbNailView} and less
 * modified as possible.
 * </p>
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public abstract class AbstractViewBasedThumbNailView extends AbstractViewBasedView {
   /**
    * Contains {@link #_lws}.
    */
   private Canvas overview;
   
   /**
    * The used {@link FixedScrollableThumbnail}.
    */
   private FixedScrollableThumbnail _thumbnail;
   
   /**
    * The used {@link LightweightSystem}.
    */
   private LightweightSystem _lws;
   
   /**
    * The {@link GraphicalViewer} of {@link #getBaseView()}.
    */
   private GraphicalViewer _graphicalViewer;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      overview = new Canvas(parent, SWT.NONE);
      _lws = new LightweightSystem(overview);
      refreshThumbnailViewer();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void handleBaseViewChanged(IViewPart oldBaseView, IViewPart newBaseView) {
      refreshThumbnailViewer();
   }
   
   /**
    * Updates the content of the current thumbnail.
    */
   protected void refreshThumbnailViewer() {
      IWorkbenchPart part = getBaseView();
      createThumbNailViewer(part);
   }
   
   /**
    * Creates a new thumbnail for the given {@link IWorkbenchPart}.
    * @param part The current {@link IWorkbenchPart}.
    */
   protected void createThumbNailViewer(IWorkbenchPart part) {
      if (_lws != null) {
         if (part != null) {
            _graphicalViewer = (GraphicalViewer) part.getAdapter(GraphicalViewer.class);
            if (_graphicalViewer != null) {
               SimpleRootEditPart rootEditPart = (SimpleRootEditPart) _graphicalViewer.getRootEditPart();
               _thumbnail = new FixedScrollableThumbnail((Viewport) rootEditPart.getFigure());
               _thumbnail.setBorder(new MarginBorder(3));
               if (rootEditPart instanceof LayerManager)
                  _thumbnail.setSource(((LayerManager) rootEditPart).getLayer(LayerConstants.PRINTABLE_LAYERS));
               _lws.setContents(_thumbnail);
            }
         } else {
            _graphicalViewer = null;
            _lws.setContents(new Figure());
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      super.dispose();
      clearThumbnail();
   }
   
   /**
    * Clears the current thumbnail.
    */
   protected void clearThumbnail() {
      if (_thumbnail != null) {
         _thumbnail.deactivate();
         _thumbnail = null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      overview.setFocus(); // Otherwise exception is thrown if focus changed from properties view to thumbnail view: WARNING: prevented recursive attempt to activate part org.eclipse.ui.views.PropertySheet while still in the middle of activating <my editor> 
   }
}