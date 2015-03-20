package org.key_project.jmlediting.core.profile.syntax;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;

/**
 * Abstract implementation of the {@link IKeywordSort}. Typically implementing
 * classes only need to define the description. Subclasses are needed because
 * the define the subsort relation of sorts.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractKeywordSort implements IKeywordSort {

   /**
    * The description of the sort.
    */
   private final String description;

   /**
    * Creates a new sort with the given description. The constructor validated
    * that the concrete class contains a valid INSTANCE field.
    *
    * @param description
    *           the description, not allowed to be null
    * @throws MalformedKeywortSortException
    *            if no valid INSTANCE field was found
    */
   protected AbstractKeywordSort(final String description) {
      if (description == null) {
         throw new IllegalArgumentException(
               "Need to give a non null description");
      }
      this.description = description;
      validateInstanceField(this);
   }

   @Override
   public String getDescription() {
      return this.description;
   }

   @Override
   public final boolean covers(final IKeywordSort other) {
      if (other == null) {
         return false;
      }
      return this.getClass().isAssignableFrom(other.getClass());
   }

   /**
    * Validates that concrete classes have a public static final INSTANCE field
    * declared which is of type of the subclass.
    */
   private static void validateInstanceField(final IKeywordSort sort)
         throws MalformedKeywortSortException {
      final Class<? extends IKeywordSort> concreteClass = sort.getClass();
      // Need to have a public static final INSTANCE field
      try {
         final Field instanceField = concreteClass.getField("INSTANCE");
         final int modifiers = instanceField.getModifiers();
         if (!Modifier.isFinal(modifiers) || !Modifier.isStatic(modifiers)
               || !Modifier.isPublic(modifiers)) {
            throw new MalformedKeywortSortException(
                  "The Sort "
                        + concreteClass.getSimpleName()
                        + " need to declare a public static final INSTANCE field of its type");
         }
         if (instanceField.getType() != concreteClass) {
            throw new MalformedKeywortSortException(
                  "The INSTANCE field of the sort "
                        + concreteClass.getSimpleName() + " is not of its type");
         }
      }
      catch (final NoSuchFieldException e) {
         throw new MalformedKeywortSortException("The sort "
               + concreteClass.getSimpleName() + " has no INSTANCE field");
      }
      catch (final SecurityException e) {
         throw new MalformedKeywortSortException(
               "Cannot access the INSTANCE field of sort "
                     + concreteClass.getSimpleName(), e);
      }

   }

   /**
    * Validates that the given sort has a valid INSTANCE field.
    *
    * @param sort
    *           the sort to validate
    * @throws MalformedKeywortSortException
    *            if the INSTANCE field is not valid or not found
    */
   public static void validateContentOfInstanceField(final IKeywordSort sort)
         throws MalformedKeywortSortException {
      validateInstanceField(sort);
      final Class<? extends IKeywordSort> concreteClass = sort.getClass();
      try {
         // Check that the value of the sort is really of this type and not of a
         // subtype
         final Field instanceField = concreteClass.getField("INSTANCE");
         final Object value = instanceField.get(null);
         if (value == null) {
            throw new MalformedKeywortSortException(
                  "The value of the INSTANCE field of sort "
                        + concreteClass.getSimpleName() + " is null.");
         }
         if (value.getClass() != concreteClass) {
            throw new MalformedKeywortSortException(
                  "The value of the INSTANCE field is not of the same type as the sort "
                        + concreteClass.getSimpleName()
                        + ". Covariant types are not supported.");
         }
      }
      catch (final NoSuchFieldException e) {
         throw new MalformedKeywortSortException("The sort "
               + concreteClass.getSimpleName() + " has no INSTANCE field");
      }
      catch (final IllegalAccessException e) {
         throw new MalformedKeywortSortException(
               "Cannot access the INSTANCE field of sort "
                     + concreteClass.getSimpleName(), e);
      }
   }

   public static <T extends IKeywordSort> T getSortObject(
         final Class<T> sortClass) {
      try {
         final Object sortObject = sortClass.getField("INSTANCE").get(null);
         return sortClass.cast(sortObject);
      }
      catch (final Exception e) {
         throw new MalformedKeywortSortException(
               "Unable to access INSTANCE field", e);
      }
   }

}
