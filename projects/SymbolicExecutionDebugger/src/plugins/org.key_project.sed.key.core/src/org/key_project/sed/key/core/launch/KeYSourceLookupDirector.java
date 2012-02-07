package org.key_project.sed.key.core.launch;

import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupDirector;
import org.eclipse.debug.core.sourcelookup.ISourceLookupParticipant;

/**
 * Implementation of {@link AbstractSourceLookupDirector} for the
 * Symbolic Execution Debugging based on KeY.
 * @author Martin Hentschel
 */
public class KeYSourceLookupDirector extends AbstractSourceLookupDirector {
    /**
     * {@inheritDoc}
     */
    @Override
    public void initializeParticipants() {
        addParticipants(new ISourceLookupParticipant[] {new KeYSourceLookupParticipant()});
    }
}
