package de.hentschel.visualdbc.statistic.ui.adapter;

import org.eclipse.core.runtime.IAdapterFactory;

import de.hentschel.visualdbc.statistic.ui.view.IProofReferencesViewPart;

/**
 * Provides a basic implementation for {@link IAdapterFactory}s that
 * allows to convert to {@link IProofReferencesViewPart}.
 * @author Martin Hentschel
 */
public abstract class AbstractProofReferenceAdapterFactory implements IAdapterFactory {
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Class[] getAdapterList() {
      return new Class[] {IProofReferencesViewPart.class};
   }
}
