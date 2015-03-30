package org.key_project.util.eclipse.swt.viewer;

import org.eclipse.jface.viewers.BaseLabelProvider;
import org.eclipse.jface.viewers.IBaseLabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.swt.widgets.Display;

/**
 * Provides basic functionality of {@link IBaseLabelProvider}.
 * @author Martin Hentschel
 */
public abstract class AbstractLabelProvider extends BaseLabelProvider {
   /**
    * Fires the event thread save via {@link #fireLabelProviderChanged(LabelProviderChangedEvent)}.
    * @param event The event to fire.
    */
   protected void fireLabelProviderChangedThreadSave(LabelProviderChangedEvent event) {
      fireLabelProviderChangedThreadSave(Display.getDefault(), event);
   }
   
   /**
    * Fires the event thread save via {@link #fireLabelProviderChanged(LabelProviderChangedEvent)}.
    * @param display The {@link Display} to fire event in.
    * @param event The event to fire.
    */
   protected void fireLabelProviderChangedThreadSave(Display display, final LabelProviderChangedEvent event) {
      display.syncExec(new Runnable() {
         @Override
         public void run() {
            fireLabelProviderChanged(event);
         }
      });
   }
}
