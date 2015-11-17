package org.key_project.sed.core.sourcesummary;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDebugTarget;

/**
 * <p>
 * An {@link ISESourceModel} provides fast access to all source regions
 * accessed during symbolic execution by an {@link ISEDebugTarget}.
 * </p>
 * <p>
 * It is available via {@link ISEDebugTarget#getSourceModel()}.
 * </p>
 * @author Martin Hentschel
 */
public interface ISESourceModel {
   /**
    * Returns all {@link ISESourceSummary}s.
    * @return All {@link ISESourceSummary}.
    */
   public ISESourceSummary[] getSourceSummaries();
   
   /**
    * Returns the {@link ISESourceSummary} for the given source {@link Object} if available.
    * @param source The source {@link Object}.
    * @return The {@link ISESourceSummary} or {@code null} if not available.
    */
   public ISESourceSummary getSourceSummary(Object source);

   /**
    * Ensures that this {@link ISESourceModel} is complete.
    * @throws DebugException Occurred Exception.
    */
   public void ensureCompleteness() throws DebugException;
   
   /**
    * Marks the model as not completed.
    */
   public void setPossiblyIncomplete();
}
