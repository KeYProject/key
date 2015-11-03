package org.key_project.javaeditor.outline;

import org.eclipse.swt.graphics.Image;

/**
 * Objects shown in an outline using the {@link OutlineContentProviderWrapper}
 * have to realize this interface to define the shown {@link Image}.
 * @author Martin Hentschel
 */
public interface IOutlineImageProvider {
   /**
    * Returns the {@link Image} to show.
    * @return The {@link Image} to show.
    */
   public Image getImage();
}
