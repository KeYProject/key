package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.dom.NodeTypes;

/**
 * This class defines node types which are used in the {@link StoreRefListParser}.
 *
 * @author Moritz Lichter
 * @see StoreRefListParser
 */
public final class StoreRefNodeTypes {

   /**
    * No instantiations.
    */
   private StoreRefNodeTypes() {

   }

   /**
    * The type for a Storage Reference Name.
    */
   public static final int STORE_REF_NAME = NodeTypes
         .getNewType("StoreRefName");
   /**
    * The type for a Storage Reference Name Suffix.
    */
   public static final int STORE_REF_NAME_SUFFIX = NodeTypes
         .getNewType("StoreRefNameSuffix");
   /**
    * The type for a Storage Reference Name Array Index.
    */
   public static final int STORE_REF_NAME_ARRAY_INDEX = NodeTypes
         .getNewType("StoreRefNameArrayIndex");
   /**
    * The type for a Storage Reference Name Array Range.
    */
   public static final int STORE_REF_NAME_ARRAY_RANGE = NodeTypes
         .getNewType("StoreRefNameArrayRange");
   /**
    * The type for a Storage Reference Name Array All (all indices).
    */
   public static final int STORE_REF_NAME_ARRAY_ALL = NodeTypes
         .getNewType("StoreRefNameArrayAll");
   /**
    * The type for a Storage Reference Expression.
    */
   public static final int STORE_REF_EXPR = NodeTypes
         .getNewType("StoreRefExpr");
   /**
    * The Type for a list of Storage Reference Expressions.
    */
   public static final int STORE_REF_LIST = NodeTypes
         .getNewType("StoreRefList");

}
