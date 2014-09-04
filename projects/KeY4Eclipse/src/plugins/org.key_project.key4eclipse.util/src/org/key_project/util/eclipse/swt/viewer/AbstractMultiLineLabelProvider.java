package org.key_project.util.eclipse.swt.viewer;

import org.eclipse.jface.viewers.OwnerDrawLabelProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Point;
import org.eclipse.swt.widgets.Event;

/**
 * Basic implementation of an {@link OwnerDrawLabelProvider} to support
 * multilined text.
 * @author Martin Hentschel
 */
public abstract class AbstractMultiLineLabelProvider extends OwnerDrawLabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   protected void measure(Event event, Object element) {
      String text = getText(element);
      if (text != null) {
         Point point = event.gc.textExtent(text);
         event.width = point.x;
         event.height = point.y;
      }
      else {
         event.width = 0;
         event.height = 0;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void paint(Event event, Object element) {
      String text = getText(element);
      if (text != null) {
         Color originalForeground = event.gc.getForeground();
         Color foregrund = getForeground(element);
         if (foregrund != null) {
            event.gc.setForeground(foregrund);
         }
         event.gc.drawText(text, event.x, event.y, true);
         event.gc.setForeground(originalForeground);
      }
   }
   
   /**
    * Returns the foreground color to use for the given element.
    * @param element The element.
    * @return The foreground color to use or {@code null} to use the default foreground color.
    */
   protected Color getForeground(Object element) {
      return null;
   }

   /**
    * Returns the text to show.
    * @param element The text to show.
    * @return
    */
   protected abstract String getText(Object element);
}
