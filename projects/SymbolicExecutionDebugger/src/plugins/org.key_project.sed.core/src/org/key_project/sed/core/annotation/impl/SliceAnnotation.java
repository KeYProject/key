package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.util.SEDAnnotationUtil;

/**
 * The {@link ISEDAnnotation} representing a slice.
 * @author Martin Hentschel
 * @see SliceAnnotationType
 */
public class SliceAnnotation extends AbstractSEDAnnotation {
   /**
    * Property {@link #getSeed()}.
    */
   public static final String PROP_SEED = "seed";
   
   /**
    * The seed.
    */
   private String seed;
   
   /**
    * Constructor.
    */
   public SliceAnnotation() {
      super(SEDAnnotationUtil.getAnnotationtype(SliceAnnotationType.TYPE_ID), true);
   }

   /**
    * Returns the seed.
    * @return The seed.
    */
   public String getSeed() {
      return seed;
   }

   /**
    * Sets the seed.
    * @param seed The seed.
    */
   public void setSeed(String seed) {
      String oldSeed = getSeed();
      this.seed = seed;
      firePropertyChange(PROP_SEED, oldSeed, getSeed());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete(ISEDDebugTarget target) {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return getSeed();
   }
}
