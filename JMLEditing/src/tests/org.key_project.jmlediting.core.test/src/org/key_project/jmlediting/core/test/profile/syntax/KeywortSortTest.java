package org.key_project.jmlediting.core.test.profile.syntax;

import static org.hamcrest.MatcherAssert.assertThat;
import static org.junit.Assert.*;

import org.junit.Test;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.MalformedKeywortSortException;
import org.key_project.jmlediting.core.test.utilities.sort.NotAccessableInstanceSort;
import org.key_project.jmlediting.core.test.utilities.sort.SortWithoutInstance;
import org.key_project.jmlediting.core.test.utilities.sort.WrongInstanceObjectSort;
import org.key_project.jmlediting.core.test.utilities.sort.WrongInstanceTypeSort;

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
   public void testSortCoversSubSort() {
      assertTrue("SubSort is covered by TopSort",
            TopSort.INSTANCE.covers(SubSort.INSTANCE));
   }

   @Test
   public void testSortCoversItseld() {
      assertTrue("Sort covers not itself",
            TopSort.INSTANCE.covers(TopSort.INSTANCE));
   }

   @Test
   public void testOtherSortNotCoversSort() {
      assertFalse("OtherSort is sub sort of TopSort",
            OtherSort.INSTANCE.covers(TopSort.INSTANCE));
      assertFalse("TopSort is sub sort of OtherSort",
            TopSort.INSTANCE.covers(OtherSort.INSTANCE));
   }

   @Test
   public void testNotCoversNull() {
      assertFalse("A null sort is never covered", TopSort.INSTANCE.covers(null));
   }

   @Test
   public void testGetDescription() {
      assertEquals("Wrong description", "Sub",
            SubSort.INSTANCE.getDescription());
   }

   @Test(expected = IllegalArgumentException.class)
   public void testNullDescription() {
      new AbstractKeywordSort(null) {
      };
   }

   private static interface IKeywortSortGetter {
      IKeywordSort getSort();
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
         public IKeywordSort getSort() {
            return new SortWithoutInstance();
         }
      });
   }

   @Test
   public void testSortNotAccessibleInstanceField() {
      testMalformedKeywortSort(new IKeywortSortGetter() {

         @Override
         public IKeywordSort getSort() {
            return new NotAccessableInstanceSort();
         }
      });

   }

   @Test
   public void testWrongTypeOfInstanceField() {
      testMalformedKeywortSort(new IKeywortSortGetter() {

         @Override
         public IKeywordSort getSort() {
            return WrongInstanceTypeSort.INSTANCE;
         }
      });
   }

   @Test
   public void testWrongInstanceFieldObject() {
      testMalformedKeywortSort(new IKeywortSortGetter() {

         @Override
         public IKeywordSort getSort() {
            return WrongInstanceObjectSort.INSTANCE;
         }
      });
   }

}
