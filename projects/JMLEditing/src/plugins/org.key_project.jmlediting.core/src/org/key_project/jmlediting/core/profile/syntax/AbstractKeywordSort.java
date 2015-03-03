package org.key_project.jmlediting.core.profile.syntax;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;

public abstract class AbstractKeywordSort implements IKeywortSort {

   private final String description;

   protected AbstractKeywordSort(final String description) {
      if (description == null) {
         throw new IllegalArgumentException(
               "Need to give a non null description");
      }
      this.description = description;
      this.validateInstanceField();
   }

   @Override
   public String getDescription() {
      return this.description;
   }

   @Override
   public final boolean isSubSortOf(final IKeywortSort other) {
      return other.getClass().isAssignableFrom(this.getClass());
   }

   /**
    * Validates that concrete classes have a public static final INSTANCE field
    * declared which is of type of the subclass.
    */
   private void validateInstanceField() {
      final Class<? extends AbstractKeywordSort> concreteClass = this
            .getClass();
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

   public static void validateContentOfInstanceField(final IKeywortSort sort) {
      final Class<? extends IKeywortSort> concreteClass = sort.getClass();
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

}
