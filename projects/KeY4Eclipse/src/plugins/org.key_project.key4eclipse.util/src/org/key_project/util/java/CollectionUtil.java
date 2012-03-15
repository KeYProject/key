package org.key_project.util.java;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;

/**
 * Provides static methods to work with {@link Collection}s.
 * @author Martin Hentschel
 */
public class CollectionUtil {
   /**
    * The default separator.
    */
   public static final String SEPARATOR = ", ";
   
   /**
    * Forbid instances by this private constructor.
    */
   private CollectionUtil() {
   }

   /**
    * Converts the {@link Collection} into a {@link String}.
    * @param collection The {@link Collection} to convert.
    * @return The {@link Collection} as {@link String}.
    */
   public static String toString(Collection<?> collection) {
      return toString(collection, SEPARATOR);
   }
   
   /**
    * Converts the {@link Collection} into a {@link String} and uses the
    * defined separator to separate elements.
    * @param collection The {@link Collection} to convert.
    * @param separator The separator between elements.
    * @return The {@link Collection} as {@link String}.
    */
   public static String toString(Collection<?> collection, String separator) {
      StringBuffer sb = new StringBuffer();
      if (collection != null) {
         boolean afterFirst = false;
         for (Object object : collection) {
            if (afterFirst) {
               if (separator != null) {
                  sb.append(separator);
               }
            }
            else {
               afterFirst = true;
            }
            sb.append(ObjectUtil.toString(object));
         }
      }
      return sb.toString();
   }

   /**
    * Nullpointersave execution of {@link Collection#isEmpty()}.
    * @param collection The given {@link Collection}.
    * @return {@code true} = is empty or {@code null}, {@code false} = is not empty.
    */
   public static boolean isEmpty(Collection<?> collection) {
      return collection == null || collection.isEmpty();
   }

   /**
    * Converts the given objects into a {@link List}.
    * @param <T> The type of the objects.
    * @param objects The objects array to convert.
    * @return The created {@link List}.
    */
   public static <T> List<T> toList(T... objects) {
      if (objects != null) {
         List<T> result = new ArrayList<T>(objects.length);
         for (T obj : objects) {
            result.add(obj);
         }
         return result;
      }
      else {
         return new ArrayList<T>(0);
      }
   }
   
   /**
    * Adds all elements to the {@link Collection}. 
    * @param <T> The type of the {@link Collection}s elements.
    * @param collection The {@link Collection} to add to.
    * @param elementsToAdd The elements to add.
    */
   public static <T> void addAll(Collection<T> collection, T... elementsToAdd) {
      if (collection != null && elementsToAdd != null) {
         for (T toAdd : elementsToAdd) {
            collection.add(toAdd);
         }
      }
   }
   
   /**
    * Removes all elements from the {@link Collection}. 
    * @param <T> The type of the {@link Collection}s elements.
    * @param collection The {@link Collection} to remove from.
    * @param elementsToRemove The elements to remove.
    * @return {@code true} if the {@link Collection} changed as result of this call.
    */
   public static <T> boolean removeAll(Collection<T> collection, T... elementsToRemove) {
      if (collection != null && elementsToRemove != null) {
         boolean result = false;
         for (T toAdd : elementsToRemove) {
            result = collection.remove(toAdd) || result;
         }
         return result;
      }
      else {
         return false;
      }
   }
   
   /**
    * Removes all occurrences of the element in the given {@link Collection}.
    * @param collection The {@link Collection} to remove from.
    * @param toRemove The element to remove.
    * @return {@code true} if at least one element was removed, {@code false} if the {@link Collection} was not modified.
    */
   public static <T> boolean removeComplete(Collection<T> collection, T toRemove) {
      if (collection != null) {
         Iterator<T> iter = collection.iterator();
         boolean changed = false;
         while (iter.hasNext()) {
            if (ObjectUtil.equals(iter.next(), toRemove)) {
               iter.remove();
               changed = true;
            }
         }
         return changed;
      }
      else {
         return false;
      }
   }

   /**
    * Searches an element in the given {@link Iterable} instance.
    * @param iterable The instance to search in.
    * @param filter The filter to select an element.
    * @return The found element or {@code null} if no element was found.
    */
   public static <T> T search(Iterable<T> iterable, IFilter<T> filter) {
      T result = null;
      if (iterable != null && filter != null) {
         Iterator<T> iter = iterable.iterator();
         if (iter != null) {
            while (result == null && iter.hasNext()) {
               T next = iter.next();
               if (filter.select(next)) {
                  result = next;
               }
            }
         }
      }
      return result;
   }

   /**
    * Checks if the given element is contained in the given {@link Iterable}.
    * @param iterable The given {@link Iterable} to search in.
    * @param element The element to search.
    * @return {@code true} = contained, {@code false} = not contained
    */
   public static <T> boolean contains(Iterable<T> iterable, T element) {
      boolean found = false;
      if (iterable != null) {
         Iterator<T> iter = iterable.iterator();
         if (iter != null) {
            while (!found && iter.hasNext()) {
               found = ObjectUtil.equals(iter.next(), element);
            }
         }
      }
      return found;
   }
   
   /**
    * Counts the number of elements in the given {@link Iterable} which
    * are selected by the given {@link IFilter}.
    * @param iterable The elements to count in.
    * @param filter The {@link IFilter} to select elements.
    * @return The number of elements selected by the {@link IFilter} in the given {@link Iterable}.
    */
   public static <T> int count(Iterable<T> iterable, IFilter<T> filter) {
      int count = 0;
      if (iterable != null && filter != null) {
         for (T element : iterable) {
            if (filter.select(element)) {
               count ++;
            }
         }
      }
      return count;
   }
}
