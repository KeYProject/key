package org.key_project.sed.key.core.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupParticipant;

/**
 * {@link AbstractSourceLookupParticipant} implementation for the
 * Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class KeYSourceLookupParticipant extends AbstractSourceLookupParticipant {
    /**
     * {@inheritDoc}
     */
    public String getSourceName(Object object) throws CoreException {
        return null; // TODO: Return the file name of the file that contains the given object.
    }
}
