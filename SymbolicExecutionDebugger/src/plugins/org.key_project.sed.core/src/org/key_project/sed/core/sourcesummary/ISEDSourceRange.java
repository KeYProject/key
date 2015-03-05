package org.key_project.sed.core.sourcesummary;

import org.key_project.sed.core.model.ISEDDebugNode;

/**
 * A source region reached during symbolic execution.
 * @author Martin Hentschel
 */
public interface ISEDSourceRange {
   /**
    * Returns the line number.
    * @return The line number. 
    */
   public int getLineNumber();
   
   /**
    * Returns the index of the start character.
    * @return The index of the start character.
    */
   public int getCharStart();
   
   /**
    * Returns the index of the end character.
    * @return The index of the end character.
    */
   public int getCharEnd();
   
   /**
    * Returns all reaching {@link ISEDDebugNode}s.
    * @return All reaching {@link ISEDDebugNode}s.
    */
   public ISEDDebugNode[] getDebugNodes();
}
