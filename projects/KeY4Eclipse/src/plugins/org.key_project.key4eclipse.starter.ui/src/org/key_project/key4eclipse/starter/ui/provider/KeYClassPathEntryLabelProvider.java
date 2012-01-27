package org.key_project.key4eclipse.starter.ui.provider;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.resources.IResource;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.key4eclipse.starter.core.property.KeYClassPathEntry;
import org.key_project.key4eclipse.util.eclipse.ResourceUtil;
import org.key_project.key4eclipse.util.java.IOUtil;

/**
 * Provides a special {@link ILabelProvider} for {@link KeYClassPathEntry} instances.
 * @author Martin Hentschel
 */
public class KeYClassPathEntryLabelProvider extends LabelProvider {
    /**
     * Contains all created images.
     */
    private Map<Object, Image> imageCache = new HashMap<Object, Image>();
    
    /**
     * {@inheritDoc}
     */
    @Override
    public String getText(Object element) {
        if (element instanceof KeYClassPathEntry) {
            return ((KeYClassPathEntry)element).getPath();
        }
        else {
            return super.getText(element);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Image getImage(Object element) {
        Image image = imageCache.get(element);
        if (image == null) {
            if (element instanceof KeYClassPathEntry) {
                KeYClassPathEntry entry = (KeYClassPathEntry)element;
                IResource resource = entry.getResource();
                if (resource != null) {
                    image = ResourceUtil.getImage(resource);
                }
                else {
                    File location = entry.getLocation();
                    image = IOUtil.getFileSystemIcon(location);
                }
            }
        }
        if (image != null) {
            imageCache.put(element, image);
            return image;
        }
        else {
            return super.getImage(element);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void dispose() {
        for (Image image : imageCache.values()) {
            image.dispose();
        }
        imageCache.clear();
        super.dispose();
    }
}
