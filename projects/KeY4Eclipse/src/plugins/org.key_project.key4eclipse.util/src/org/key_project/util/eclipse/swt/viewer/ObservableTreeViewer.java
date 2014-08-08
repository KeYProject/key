package org.key_project.util.eclipse.swt.viewer;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Item;
import org.eclipse.swt.widgets.Tree;
import org.eclipse.swt.widgets.TreeItem;
import org.key_project.util.eclipse.swt.viewer.event.IViewerUpdateListener;
import org.key_project.util.eclipse.swt.viewer.event.ViewerUpdateEvent;

/**
 * This {@link TreeViewer} allows to observe the event when a {@link TreeItem}
 * is updated. This for instance important when lazy provider are used.
 * @author Martin Hentschel
 */
public class ObservableTreeViewer extends TreeViewer {
   /**
    * All registered {@link IViewerUpdateListener}.
    */
   private final List<IViewerUpdateListener> updateListener = new LinkedList<IViewerUpdateListener>();

   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    */
   public ObservableTreeViewer(Composite parent, int style) {
      super(parent, style);
   }

   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    */
   public ObservableTreeViewer(Composite parent) {
      super(parent);
   }

   /**
    * Constructor.
    * @param tree The {@link Tree} to use.
    */
   public ObservableTreeViewer(Tree tree) {
      super(tree);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void doUpdateItem(Item item, Object element) {
      super.doUpdateItem(item, element);
      fireItemUpdated(new ViewerUpdateEvent(this, item, element));
   }
   
   /**
    * Adds the given {@link IViewerUpdateListener}.
    * @param l The {@link IViewerUpdateListener} to add.
    */
   public void addViewerUpdateListener(IViewerUpdateListener l) {
      if (l != null) {
         updateListener.add(l);
      }
   }

   /**
    * Removes the given {@link IViewerUpdateListener}.
    * @param l The {@link IViewerUpdateListener} to remove.
    */
   public void removeViewerUpdateListener(IViewerUpdateListener l) {
      if (l != null) {
         updateListener.remove(l);
      }
   }
   
   /**
    * Returns all available {@link IViewerUpdateListener}.
    * @return All available {@link IViewerUpdateListener}.
    */
   public IViewerUpdateListener[] getViewerUpdateListeners() {
      return updateListener.toArray(new IViewerUpdateListener[updateListener.size()]);
   }
   
   /**
    * Fires the event {@link IViewerUpdateListener#itemUpdated(ViewerUpdateEvent)} to all listener.
    * @param e The event to fire.
    */
   protected void fireItemUpdated(ViewerUpdateEvent e) {
      IViewerUpdateListener[] toInfor = getViewerUpdateListeners();
      for (IViewerUpdateListener l : toInfor) {
         l.itemUpdated(e);
      }
   }
}
