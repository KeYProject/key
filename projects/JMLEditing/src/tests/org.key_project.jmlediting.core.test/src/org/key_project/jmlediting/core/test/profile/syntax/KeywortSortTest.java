package org.key_project.jmlediting.core.test.profile.syntax;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.Assert.*;

import org.junit.Test;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.core.profile.syntax.MalformedKeywortSortException;

public class KeywortSortTest {

   public static class TopSort extends AbstractKeywordSort {
      public static final TopSort INSTANCE = new TopSort();

      private TopSort() {
         super("Top");
      }

      protected TopSort(final String description) {
         super(description);
      }

   }

   public static class SubSort extends TopSort {
      public static final SubSort INSTANCE = new SubSort();

      private SubSort() {
         super("Sub");
      }
   }

   public static class OtherSort extends AbstractKeywordSort {

      public static final OtherSort INSTANCE = new OtherSort();

      protected OtherSort() {
         super("Other");
      }
   }

   @Test
   public void testSubSortIsSubSort() {
      assertTrue("SubSort is a sub sort of TopSort",
            SubSort.INSTANCE.isSubSortOf(TopSort.INSTANCE));
   }

   @Test
   public void testOtherSortIsNotSubSort() {
      assertFalse("OtherSort is sub sort of TopSort",
            OtherSort.INSTANCE.isSubSortOf(TopSort.INSTANCE));
      assertFalse("TopSort is sub sort of OtherSort",
            TopSort.INSTANCE.isSubSortOf(OtherSort.INSTANCE));
   }

   @Test
   public void testGetDescription() {
      assertEquals("Wrong description", "Sub",
            SubSort.INSTANCE.getDescription());
   }

   private static interface IKeywortSortGetter {
      IKeywortSort getSort();
   }

   private static void testMalformedKeywortSort(final IKeywortSortGetter test) {
      try {
         test.getSort();
         fail("No exception but expected ExceptionInInitializerError");
      }
      catch (final ExceptionInInitializerError e) {
         assertThat("Expected a MalformedKeywortSortException",
               e.getCause() instanceof MalformedKeywortSortException);
      }
      catch (final MalformedKeywortSortException e) {

      }
   }

   @Test
   public void testSortWithoutInstance() {
      testMalformedKeywortSort(new IKeywortSortGetter() {

         @Override
         public IKeywortSort getSort() {
            return new SortWithoutInstance();
         }
      });
   }

   @Test
   public void testSortNotAccessibleInstanceField() {
      testMalformedKeywortSort(new IKeywortSortGetter() {

         @Override
         public IKeywortSort getSort() {
            return NotAccessableInstanceSort.INSTANCE;
         }
      });

   }

   @Test
   public void testWrongTypeOfInstanceField() {
      testMalformedKeywortSort(new IKeywortSortGetter() {

         @Override
         public IKeywortSort getSort() {
            return WrongInstanceTypeSort.INSTANCE;
         }
      });
   }

   @Test
   public void testWrongInstanceFieldObject() {
      testMalformedKeywortSort(new IKeywortSortGetter() {

         @Override
         public IKeywortSort getSort() {
            return WrongInstanceObjectSort.INSTANCE;
         }
      });
   }

}
