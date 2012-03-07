package org.key_project.sed.core.test.example.fixed_launch_content;

import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupDirector;
import org.eclipse.debug.core.sourcelookup.ISourceLookupParticipant;

/**
 * Implementation of {@link AbstractSourceLookupDirector} for the
 * fixed example.
 * @author Martin Hentschel
 */
public class FixedExampleSourceLookupDirector extends AbstractSourceLookupDirector {
    /**
     * {@inheritDoc}
     */
    @Override
    public void initializeParticipants() {
        addParticipants(new ISourceLookupParticipant[] {new FixedExampleSourceLookupParticipant()});
    }
}
