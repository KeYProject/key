package org.key_project.sed.key.core.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupParticipant;
import org.key_project.sed.core.model.ISourceNameProvider;

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
      if (object instanceof IAdaptable) {
         ISourceNameProvider provider = (ISourceNameProvider)((IAdaptable)object).getAdapter(ISourceNameProvider.class);
         return provider != null ? provider.getSourceName() : null;
      }
      else {
         return null;
      }
   }
}
