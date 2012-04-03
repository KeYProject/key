package org.key_project.sed.ui.visualization.execution_tree.service;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.graphiti.features.impl.IIndependenceSolver;
import org.eclipse.graphiti.ui.features.DefaultFeatureProvider;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Implementation of {@link IIndependenceSolver} which can be used to link
 * non EMF objects with graphiti diagram elements. This implementation does
 * the mapping via the non EMF object hash codes ({@link Object#hashCode()}).
 * </p>
 * <p>
 * To use this {@link IIndependenceSolver} it is required to change the
 * default instance in the constructor of the used {@link DefaultFeatureProvider}
 * via {@code setIndependenceSolver}.
 * </p>
 * @author Martin Hentschel
 */
public class HashCodeIndependenceSolver implements IIndependenceSolver {
   /**
    * Maps the hash code ({@link Object#hashCode()}) to his instance.
    */
   private Map<String, Object> objectHashmap = new HashMap<String, Object>();

   /**
    * {@inheritDoc}
    */
   @Override
   public String getKeyForBusinessObject(Object bo) {
      String key = Integer.toString(ObjectUtil.hashCode(bo));
      objectHashmap.put(key, bo);
      return key;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getBusinessObjectForKey(String key) {
      return key != null ? objectHashmap.get(key) : null;
   }
   
   /**
    * Returns all known business objects.
    * @return The known business objects.
    */
   public Collection<Object> getAllBusinessObjects() {
      return objectHashmap.values();
   }
}
