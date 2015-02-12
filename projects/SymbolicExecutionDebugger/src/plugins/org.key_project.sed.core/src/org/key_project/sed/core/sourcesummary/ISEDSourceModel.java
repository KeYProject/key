package org.key_project.sed.core.sourcesummary;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugTarget;

/**
 * <p>
 * An {@link ISEDSourceModel} provides fast access to all source regions
 * accessed during symbolic execution by an {@link ISEDDebugTarget}.
 * </p>
 * <p>
 * It is available via {@link ISEDDebugTarget#getSourceModel()}.
 * </p>
 * @author Martin Hentschel
 */
public interface ISEDSourceModel {
   /**
    * Returns all {@link ISEDSourceSummary}s.
    * @return All {@link ISEDSourceSummary}.
    */
   public ISEDSourceSummary[] getSourceSummaries();
   
   /**
    * Returns the {@link ISEDSourceSummary} for the given source {@link Object} if available.
    * @param source The source {@link Object}.
    * @return The {@link ISEDSourceSummary} or {@code null} if not available.
    */
   public ISEDSourceSummary getSourceSummary(Object source);

   /**
    * Ensures that this {@link ISEDSourceModel} is complete.
    * @throws DebugException Occurred Exception.
    */
   public void ensureCompleteness() throws DebugException;
   
   /**
    * Marks the model as not completed.
    */
   public void setPossiblyIncomplete();
}
