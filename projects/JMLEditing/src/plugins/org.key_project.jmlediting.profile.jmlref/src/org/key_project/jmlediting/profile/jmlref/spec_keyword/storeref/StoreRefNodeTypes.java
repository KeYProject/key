package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import org.key_project.jmlediting.core.dom.NodeTypes;

/**
 * This class defines node types which are used in the {@link StoreRefParser}.
 *
 * @author Moritz Lichter
 * @see StoreRefParser
 */
public class StoreRefNodeTypes {

   public static final int STORE_REF_NAME = NodeTypes
         .getNewType("StoreRefName");
   public static final int STORE_REF_NAME_SUFFIX = NodeTypes
         .getNewType("StoreRefNameSuffix");
   public static final int STORE_REF_NAME_ARRAY_INDEX = NodeTypes
         .getNewType("StoreRefNameArrayIndex");
   public static final int STORE_REF_NAME_ARRAY_RANGE = NodeTypes
         .getNewType("StoreRefNameArrayRange");
   public static final int STORE_REF_NAME_ARRAY_ALL = NodeTypes
         .getNewType("StoreRefNameArrayAll");
   public static final int STORE_REF_EXPR = NodeTypes
         .getNewType("StoreRefExpr");
   public static final int STORE_REF_LIST = NodeTypes
         .getNewType("StoreRefList");

}
