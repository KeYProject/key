package org.key_project.jmlediting.core.test.profile.syntax;

import java.util.Collections;

import org.junit.Test;
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.EmptyKeywordContent;
import org.key_project.jmlediting.core.profile.syntax.user.UserDefinedKeyword;

public class UserDefinedKeywordTest {

   @Test(expected = IllegalArgumentException.class)
   public void testNoContent() {
      new UserDefinedKeyword(Collections.singleton("a"),
            ToplevelKeywordSort.INSTANCE, null, "dasd", null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testNoSort() {
      new UserDefinedKeyword(Collections.singleton("a"), null,
            new EmptyKeywordContent(), "dasd", null);
   }

   @Test(expected = IllegalArgumentException.class)
   public void testNoDescription() {
      new UserDefinedKeyword(Collections.singleton("a"),
            ToplevelKeywordSort.INSTANCE, new EmptyKeywordContent(), null, null);
   }

}
