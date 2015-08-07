package org.key_project.sed.key.evaluation.server.index;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.CollectionUtil;

/**
 * A {@link PermutationIndex} stores for each possible permutation of given
 * elements a data value creates by an {@link IDataFactory}.
 * <p>
 * The mapping of a permutation to its data object is represented by an {@link Entry}.
 * <p>
 * The entries in the index are sorted by the given data {@link Comparator}.
 * <p>
 * The data of the first {@link Entry} can be updated thread save via
 * {@link #updateFirstEntry(IEntryUpdater)}.
 * @author Martin Hentschel
 * @param <E> The type of the elements.
 * @param <D> The type of the data.
 */
public class PermutationIndex<E, D> {
   /**
    * The indexed {@link Entry} instances.
    */
   private final List<Entry<E, D>> index;
   
   /**
    * The used {@link Comparator} to compare {@link Entry} instances.
    */
   private final Comparator<Entry<E, D>> entryComparator;
   
   /**
    * Constructor.
    * @param elements The elements to index its permutations.
    * @param dataFactory The {@link IDataFactory} to use to create initial data objects.
    * @param entryComparator The {@link Comparator} to compare {@link Entry} instances.
    */
   public PermutationIndex(E[] elements, IDataFactory<E, D> dataFactory, Comparator<Entry<E, D>> entryComparator) {
      this.entryComparator = entryComparator;
      E[][] permutations = ArrayUtil.generatePermutations(elements);
      this.index = Collections.synchronizedList(new ArrayList<Entry<E, D>>(permutations.length));
      for (E[] permutation : permutations) {
         D data = dataFactory.createData(permutation);
         Entry<E, D> entry = new Entry<E, D>(permutation, data);
         CollectionUtil.binaryInsert(index, entry, entryComparator);
      }
   }

   /**
    * Returns the used {@link Comparator} to compare {@link Entry} instances.
    * @return The used {@link Comparator} to compare {@link Entry} instances.
    */
   public Comparator<Entry<E, D>> getEntryComparator() {
      return entryComparator;
   }

   /**
    * Returns the size of the index which is the number of permutations.
    * @return The size of the index.
    */
   public int size() {
      return index.size();
   }
   
   /**
    * Returns a read-only view of the index.
    * @return A read-only view of the index.
    */
   public List<Entry<E, D>> getIndex() {
      return Collections.unmodifiableList(index);
   }
   
   /**
    * Allows to modify the data object of the first {@link Entry} in the
    * index thread save. The index is updated after modification.
    * @param updater The {@link IEntryUpdater} to perform.
    */
   public void updateFirstEntry(IEntryUpdater<E, D> updater) {
      synchronized (index) {
         Entry<E, D> updatedEntry = updater.updateEntry(index);
         if (updatedEntry != null) {
            if (!index.remove(updatedEntry)) {
               throw new IllegalStateException("Entry is not conained in index.");
            }
            CollectionUtil.binaryInsert(index, updatedEntry, entryComparator);
         }
      }
   }

   /**
    * Print the index into the console.
    */
   public void print() {
      System.out.println("Size: " + size());
      for (Entry<E, D> entry : index) {
         System.out.println(entry);
      }
   }
   
   /**
    * Modifies a given {@link Entry}.
    * @author Martin Hentschel
    */
   public static interface IEntryUpdater<E, D> {
      /**
       * Modifies an {@link Entry} of the given {@link List}.
       * @param list The sorted {@link List} with the available {@link Entry}s.
       * @return The updated {@link Entry} or {@code null} if no {@link Entry} was updated.
       */
      public Entry<E, D> updateEntry(List<Entry<E, D>> list);
   }

   /**
    * The maps a permutation to its data object.
    * @author Martin Hentschel
    */
   public static final class Entry<E, D> {
      /**
       * The permutation.
       */
      private final E[] permutation;
      
      /**
       * The data object.
       */
      private final D data;

      /**
       * Constructor.
       * @param permutation The permutation.
       * @param data The data object.
       */
      public Entry(E[] permutation, D data) {
         this.permutation = permutation;
         this.data = data;
      }

      /**
       * Returns the permutation.
       * @return The permutation.
       */
      public E[] getPermutation() {
         return permutation;
      }

      /**
       * Returns the data object.
       * @return The data object.
       */
      public D getData() {
         return data;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return ArrayUtil.toString(permutation) + ": " + data;
      }
   }
   
   /**
    * Factory to create data objects.
    * @author Martin Hentschel
    */
   public static interface IDataFactory<E, D> {
      public D createData(E[] permutation);
   }
}
