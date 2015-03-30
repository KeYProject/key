package org.key_project.util.eclipse.swt.viewer.event;

import java.util.EventListener;

import org.eclipse.jface.viewers.Viewer;
import org.eclipse.swt.widgets.Item;

/**
 * Allows to observe updates on {@link Item}s of a {@link Viewer}.
 * @author Martin Hentschel
 */
public interface IViewerUpdateListener extends EventListener {
   /**
    * When an {@link Item} was updated.
    * @param e The event.
    */
   public void itemUpdated(ViewerUpdateEvent e);
}
