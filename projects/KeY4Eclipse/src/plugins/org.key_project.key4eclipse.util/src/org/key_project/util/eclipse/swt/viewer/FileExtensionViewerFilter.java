package org.key_project.util.eclipse.swt.viewer;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.resources.IContainer;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jface.viewers.Viewer;
import org.eclipse.jface.viewers.ViewerFilter;
import org.key_project.util.Activator;
import org.key_project.util.eclipse.Logger;
import org.key_project.util.java.StringUtil;

/**
 * This {@link ViewerFilter} can be used to filter {@link IFile}s by 
 * their file extensions ({@link IFile#getFileExtension()}).
 * @author Martin Hentschel
 */
public class FileExtensionViewerFilter extends ViewerFilter {
    /**
     * The accepted file extensions in lower case.
     */
    private Set<String> acceptedExtensions = new HashSet<String>();
    
    /**
     * Constructor.
     * @param acceptedExtensions The allowed file extensions.
     */
    public FileExtensionViewerFilter(String[] acceptedExtensions) {
        super();
        // Convert all file extension into lower case.
        if (acceptedExtensions != null) {
            for (String extension : acceptedExtensions) {
                if (extension != null) {
                    this.acceptedExtensions.add(extension.toLowerCase());
                }
                else {
                    this.acceptedExtensions.add(StringUtil.EMPTY_STRING);
                }
            }
        }
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean select(Viewer viewer, Object parentElement, Object element) {
        try {
            if (element instanceof IFile) {
                // Check file extension
                IFile file = (IFile)element;
                String extension = file.getFileExtension();
                if (extension == null) {
                    extension = StringUtil.EMPTY_STRING;
                }
                else {
                    extension = extension.toLowerCase();
                }
                return acceptedExtensions.contains(extension);
            }
            else if (element instanceof IContainer) {
                // Make sure that it contains an accepted file.
                IResource[] children = ((IContainer)element).members();
                boolean childAccepted = false;
                int i = 0;
                while (!childAccepted && i < children.length) {
                    childAccepted = select(viewer, element, children[i]);
                    i++;
                }
                return childAccepted;
            }
            else {
                return false; // Unknown elements.
            }
        }
        catch (CoreException e) {
            new Logger(Activator.getDefault(), Activator.PLUGIN_ID).logError(e);
            return false;
        }
    }
}
