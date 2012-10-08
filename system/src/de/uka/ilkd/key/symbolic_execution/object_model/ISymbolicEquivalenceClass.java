package de.uka.ilkd.key.symbolic_execution.object_model;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.logic.Term;

/**
 * An equivalence class which defines which {@link Term}s represent
 * the same {@link ISymbolicObject} in an {@link ISymbolicConfiguration}.
 * @author Martin Hentschel
 */
public interface ISymbolicEquivalenceClass {
   /**
    * Returns the terms which represents the same {@link ISymbolicObject}.
    * @return The terms which represents the same {@link ISymbolicObject}.
    */
   public ImmutableList<Term> getTerms();
   
   /**
    * Checks if a {@link Term} is contained.
    * @param term The {@link Term} to check.
    * @return {@code true} {@link Term} is contained, {@code false} {@link Term} is not contained.
    */
   public boolean containsTerm(Term term);
   
   /**
    * Returns the terms which represents the same {@link ISymbolicObject} as human readable {@link String}.
    * @return The terms which represents the same {@link ISymbolicObject} as human readable {@link String}.
    */
   public ImmutableList<String> getTermStrings();
   
   /**
    * Returns the most representative term.
    * @return The most representative term.
    */
   public Term getRepresentative();

   /**
    * Returns the most representative term as human readable {@link String}.
    * @return The most representative term as human readable {@link String}.
    */
   public String getRepresentativeString();
}
