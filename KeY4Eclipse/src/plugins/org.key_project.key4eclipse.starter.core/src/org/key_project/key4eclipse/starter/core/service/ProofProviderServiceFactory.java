package org.key_project.key4eclipse.starter.core.service;

import org.eclipse.ui.IPartService;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.services.AbstractServiceFactory;
import org.eclipse.ui.services.IServiceLocator;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;

/**
 * An {@link AbstractServiceFactory} to retrieve {@link IProofProvider} instances of the active {@link IWorkbenchPart}.
 * @author Martin Hentschel
 */
public class ProofProviderServiceFactory extends AbstractServiceFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object create(@SuppressWarnings("rawtypes") Class serviceInterface, 
                        IServiceLocator parentLocator, 
                        IServiceLocator locator) {
      IPartService ps = (IPartService) locator.getService(IPartService.class);
      if (ps != null) {
         IWorkbenchPart wp = ps.getActivePart();
         return wp.getAdapter(IProofProvider.class);
      }
      else {
         return null;
      }
   }
}
