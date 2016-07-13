/**
 * 
 */
package org.key_project.sed.core.model;

/**
 * An {@link ISENodeLink} instance is an additional link between two {@link ISENode}s.
 * @author Martin Hentschel
 */
public interface ISENodeLink extends ISEDebugElement {
   /**
    * Returns the source {@link ISENode}.
    * @return The source {@link ISENode}.
    */
   public ISENode getSource();
   
   /**
    * Returns the target {@link ISENode}.
    * @return The target {@link ISENode}.
    */
   public ISENode getTarget();
   
   /**
    * Returns the name.
    * @return The name.
    */
   public String getName();
}
