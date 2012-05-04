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
      Canvas overview = new Canvas(parent, SWT.NONE);
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
   }
}
