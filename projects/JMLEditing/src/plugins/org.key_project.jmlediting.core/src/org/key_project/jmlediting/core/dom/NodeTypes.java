package org.key_project.jmlediting.core.dom;

import java.util.HashMap;

public final class NodeTypes {

   private static HashMap<Integer, String> typeNames = new HashMap<Integer, String>();

   private static int newType = Integer.MIN_VALUE;

   public static final int STRING = getNewType("String");
   public static final int KEYWORD = getNewType("Keyword");
   public static final int KEYWORD_APPL = getNewType("KeywordAppl");
   public static final int KEYWORD_CONTENT = getNewType("KeywordContent");
   public static final int NODE = getNewType("Node");
   public static final int LIST = getNewType("List");
   public static final int SEQ = getNewType("Seq");
   public static final int SOME = getNewType("Some");
   public static final int NONE = getNewType("None");

   public static final int ERROR_NODE = getNewType("ErrorNode");
   public static final int UNPARSED_TEXT = getNewType("UnparsedText");

   public static int getNewType(final String name) {
      final int type = newType;
      typeNames.put(type, name);
      newType++;
      return type;
   }

   public static String getTypeName(final int type) {
      return typeNames.get(type);
   }

}
