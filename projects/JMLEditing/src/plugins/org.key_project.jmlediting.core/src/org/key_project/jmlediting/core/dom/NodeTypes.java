package org.key_project.jmlediting.core.dom;

public final class NodeTypes {

   public static final int STRING = getNewType();
   public static final int KEYWORD = getNewType();
   public static final int KEYWORD_APPL = getNewType();
   public static final int NODE = getNewType();
   public static final int LIST = getNewType();
   public static final int SEQ = getNewType();

   private static int newType = Integer.MIN_VALUE;

   public static int getNewType() {
      final int type = newType;
      newType++;
      return type;
   }
}
