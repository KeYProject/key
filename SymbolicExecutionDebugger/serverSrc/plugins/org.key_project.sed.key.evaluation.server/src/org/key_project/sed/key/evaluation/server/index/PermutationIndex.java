package org.key_project.sed.key.evaluation.server.index;

import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedList;
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
   private final List<Entry<E, D>> index = Collections.synchronizedList(new LinkedList<Entry<E, D>>());
   
   /**
    * The used {@link Comparator} to compare data objects.
    */
   private final Comparator<D> dataComparator;
   
   /**
    * The used {@link Comparator} to compare {@link Entry} instances.
    */
   private final Comparator<Entry<E, D>> entryComparator = new Comparator<Entry<E, D>>() {
      @Override
      public int compare(Entry<E, D> o1, Entry<E, D> o2) {
         return dataComparator.compare(o1.getData(), o2.getData());
      }
   };
   
   /**
    * Constructor.
    * @param elements The elements to index its permutations.
    * @param dataFactory The {@link IDataFactory} to use to create initial data objects.
    * @param dataComparator The {@link Comparator} to use to compare data objects.
    */
   public PermutationIndex(E[] elements, IDataFactory<E, D> dataFactory, Comparator<D> dataComparator) {
      this.dataComparator = dataComparator;
      E[][] permutations = ArrayUtil.generatePermutations(elements);
      for (E[] permutation : permutations) {
         D data = dataFactory.createData(permutation);
         Entry<E, D> entry = new Entry<E, D>(permutation, data);
         CollectionUtil.binaryInsert(index, entry, entryComparator);
      }
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
    * Returns the used data {@link Comparator}.
    * @return The used data {@link Comparator}.
    */
   public Comparator<D> getDataComparator() {
      return dataComparator;
   }
   
   /**
    * Allows to modify the data object of the first {@link Entry} in the
    * index thread save. The index is updated after modification.
    * @param updater The {@link IEntryUpdater} to perform.
    */
   public void updateFirstEntry(IEntryUpdater<E, D> updater) {
      synchronized (index) {
         Entry<E, D> entry = index.get(0);
         if (updater.updateFirstEntry(entry)) {
            if (!index.remove(entry)) {
               throw new IllegalStateException("First entry is not available.");
            }
            CollectionUtil.binaryInsert(index, entry, entryComparator);
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
       * Modifies the given {@link Entry}.
       * @param firstEntry The given {@link Entry} to modify.
       * @return {@code true} index needs to be updated, {@code false} index should stay as it is.
       */
      public boolean updateFirstEntry(Entry<E, D> firstEntry);
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
