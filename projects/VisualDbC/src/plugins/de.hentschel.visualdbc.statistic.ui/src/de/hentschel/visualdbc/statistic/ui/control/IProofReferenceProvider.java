package de.hentschel.visualdbc.statistic.ui.control;

import java.util.List;

/**
 * Defines the methods that are required to show content 
 * in a {@link ProofReferenceComposite}.
 * @author Martin Hentschel
 */
public interface IProofReferenceProvider {
   /**
    * Extracts the elements to show from the given one.
    * @param elements The given elements.
    * @return The elements to show.
    */
   public List<?> extractElementsToShow(List<?> elements);

   /**
    * Selects the given elements in the provider.
    * @param toSelect The elements to select.
    */
   public void select(List<?> toSelect);
}
