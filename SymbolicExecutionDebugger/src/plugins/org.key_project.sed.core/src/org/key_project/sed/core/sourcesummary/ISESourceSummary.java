package org.key_project.sed.core.sourcesummary;

/**
 * Provides fast access to all source regions of a single source file
 * accessed during symbolic execution.
 * @author Martin Hentschel
 */
public interface ISESourceSummary {
   /**
    * Returns the source object.
    * @return The source object.
    */
   public Object getSource();
   
   /**
    * Returns all {@link ISESourceRange}s accessed during symbolic execution.
    * @return All {@link ISESourceRange}s accessed during symbolic execution.
    */
   public ISESourceRange[] getSourceRanges();
   
   /**
    * Returns the {@link ISESourceRange} for specified range if available.
    * @param lineNumber The line number.
    * @param charStart The index of the start character.
    * @param charEnd The index of the end character.
    * @return The {@link ISESourceRange} or {@code null} if not available.
    */
   public ISESourceRange getSourceRange(int lineNumber, int charStart, int charEnd);
}
