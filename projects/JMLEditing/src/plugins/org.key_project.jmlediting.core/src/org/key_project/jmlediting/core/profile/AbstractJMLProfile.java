package org.key_project.jmlediting.core.profile;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

/**
 * This class implements some methods of the {@link IJMLProfile} in a generic
 * way.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractJMLProfile implements IJMLProfile {

   /**
    * Helper class for a tuple of key and type class.
    * 
    * @author Moritz Lichter
    *
    */
   private static class TypedKey {
      private final Object key;
      private final Class<?> contentType;

      private TypedKey(final Object key, final Class<?> contentType) {
         super();
         this.key = key;
         this.contentType = contentType;
      }

      @Override
      public int hashCode() {
         final int prime = 31;
         int result = 1;
         result = prime * result
               + ((this.contentType == null) ? 0 : this.contentType.hashCode());
         result = prime * result
               + ((this.key == null) ? 0 : this.key.hashCode());
         return result;
      }

      @Override
      public boolean equals(final Object obj) {
         if (this == obj) {
            return true;
         }
         if (obj == null) {
            return false;
         }
         if (this.getClass() != obj.getClass()) {
            return false;
         }
         final TypedKey other = (TypedKey) obj;
         if (this.contentType == null) {
            if (other.contentType != null) {
               return false;
            }
         }
         else if (!this.contentType.equals(other.contentType)) {
            return false;
         }
         if (this.key == null) {
            if (other.key != null) {
               return false;
            }
         }
         else if (!this.key.equals(other.key)) {
            return false;
         }
         return true;
      }

   }

   /**
    * A map which stores the extensions registered to this profile.
    */
   private final Map<TypedKey, Set<?>> extensions = new HashMap<TypedKey, Set<?>>();

   @Override
   public <T> Set<T> getExtensions(final Object key, final Class<T> clazz) {
      @SuppressWarnings("unchecked")
      final Set<T> extensionSet = (Set<T>) this.extensions.get(new TypedKey(
            key, clazz));
      if (extensionSet == null) {
         return Collections.emptySet();
      }
      return extensionSet;

   }

   /**
    * Allows subclasses to put an extension to the profile.
    *
    * @param key
    *           the key object
    * @param newValue
    *           the new value
    * @param clazz
    *           the type class
    * @param <T>
    *           the type of the extension
    */
   protected <T> void putExtension(final Object key, final T newValue,
         final Class<T> clazz) {
      final TypedKey tKey = new TypedKey(key, clazz);
      @SuppressWarnings("unchecked")
      Set<T> extensionSet = (Set<T>) this.extensions.get(tKey);
      if (extensionSet == null) {
         extensionSet = new HashSet<T>();
      }
      extensionSet.add(newValue);
      this.extensions.put(tKey, extensionSet);
   }
}
