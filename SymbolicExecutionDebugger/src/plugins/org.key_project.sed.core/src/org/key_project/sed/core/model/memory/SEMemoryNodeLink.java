package org.key_project.sed.core.model.memory;

import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISENodeLink;
import org.key_project.sed.core.model.impl.AbstractSENodeLink;

/**
 * Implementation of {@link ISENodeLink} that stores all
 * information in the memory.
 * @author Martin Hentschel
 */
public class SEMemoryNodeLink extends AbstractSENodeLink {
   /**
    * The source {@link ISENode}.
    */
   private ISENode source;
   
   /**
    * The target {@link ISENode}.
    */
   private ISENode target;
   
   /**
    * The name.
    */
   private String name;

   /**
    * Constructor.
    * @param target The {@link ISEDebugTarget} in that this method return is contained.
    */
   public SEMemoryNodeLink(ISEDebugTarget target) {
      super(target);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISENode getSource() {
      return source;
   }

   /**
    * Sets the source.
    * @param source The source to set.
    */
   public void setSource(ISENode source) {
      this.source = source;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISENode getTarget() {
      return target;
   }

   /**
    * Sets the target.
    * @param target The target to set.
    */
   public void setTarget(ISENode target) {
      this.target = target;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return name;
   }

   /**
    * Sets the name.
    * @param name The name to set.
    */
   public void setName(String name) {
      this.name = name;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setId(String id) {
      super.setId(id);
   }
}
