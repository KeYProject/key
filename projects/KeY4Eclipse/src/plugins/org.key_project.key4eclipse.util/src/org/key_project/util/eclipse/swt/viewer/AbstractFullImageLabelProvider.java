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

package org.key_project.util.eclipse.swt.viewer;

import org.eclipse.jface.viewers.OwnerDrawLabelProvider;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.graphics.Image;
import org.eclipse.swt.widgets.Event;

/**
 * A basic implementation of a {@link OwnerDrawLabelProvider} which shows {@link Image}s.
 * @author Martin Hentschel
 */
public abstract class AbstractFullImageLabelProvider extends OwnerDrawLabelProvider {
   /**
    * {@inheritDoc}
    */
   @Override
   protected void measure(Event event, Object element) {
      Image image = getImage(element, event.index, event.gc.getBackground(), event.gc.getForeground());
      if (image != null) {
         event.width = image.getImageData().width;
         event.height = image.getImageData().height;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void paint(Event event, Object element) {
      Image image = getImage(element, event.index, event.gc.getBackground(), event.gc.getForeground());
      if (image != null) {
         event.gc.drawImage(image, event.x, event.y);
      }
   }

   /**
    * Returns the {@link Image} to show.
    * @param element The element.
    * @param index The column index.
    * @param background The background {@link Color} to use.
    * @param foreground The foreground {@link Color} to use.
    * @return The {@link Image} to show or {@code null} if nothing should be shown.
    */
   protected abstract Image getImage(Object element, 
                                     int index, 
                                     Color background,
                                     Color foreground);
}
