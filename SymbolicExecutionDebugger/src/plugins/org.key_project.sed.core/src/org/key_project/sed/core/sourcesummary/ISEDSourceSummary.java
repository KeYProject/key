package org.key_project.sed.core.sourcesummary;

/**
 * Provides fast access to all source regions of a single source file
 * accessed during symbolic execution.
 * @author Martin Hentschel
 */
public interface ISEDSourceSummary {
   /**
    * Returns the source object.
    * @return The source object.
    */
   public Object getSource();
   
   /**
    * Returns all {@link ISEDSourceRange}s accessed during symbolic execution.
    * @return All {@link ISEDSourceRange}s accessed during symbolic execution.
    */
   public ISEDSourceRange[] getSourceRanges();
   
   /**
    * Returns the {@link ISEDSourceRange} for specified range if available.
    * @param lineNumber The line number.
    * @param charStart The index of the start character.
    * @param charEnd The index of the end character.
    * @return The {@link ISEDSourceRange} or {@code null} if not available.
    */
   public ISEDSourceRange getSourceRange(int lineNumber, int charStart, int charEnd);
}
