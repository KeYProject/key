package org.key_project.sed.core.test.example.fixed_launch_content;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupParticipant;

/**
 * {@link AbstractSourceLookupParticipant} implementation for the
 * fixed example.
 * @author Martin Hentschel
 */
public class FixedExampleSourceLookupParticipant extends AbstractSourceLookupParticipant {
    /**
     * {@inheritDoc}
     */
    public String getSourceName(Object object) throws CoreException {
        return null;
    }
}
