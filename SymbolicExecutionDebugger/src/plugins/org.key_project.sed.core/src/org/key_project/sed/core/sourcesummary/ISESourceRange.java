package org.key_project.sed.core.sourcesummary;

import org.key_project.sed.core.model.ISENode;

/**
 * A source region reached during symbolic execution.
 * @author Martin Hentschel
 */
public interface ISESourceRange {
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
    * Returns all reaching {@link ISENode}s.
    * @return All reaching {@link ISENode}s.
    */
   public ISENode[] getDebugNodes();
}
