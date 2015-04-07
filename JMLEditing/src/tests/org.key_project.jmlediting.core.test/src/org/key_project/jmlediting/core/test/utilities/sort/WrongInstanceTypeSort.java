package org.key_project.jmlediting.core.test.utilities.sort;

import org.key_project.jmlediting.core.test.profile.syntax.KeywortSortTest.OtherSort;

public class WrongInstanceTypeSort extends OtherSort {
   public static final OtherSort INSTANCE = new WrongInstanceTypeSort();
}