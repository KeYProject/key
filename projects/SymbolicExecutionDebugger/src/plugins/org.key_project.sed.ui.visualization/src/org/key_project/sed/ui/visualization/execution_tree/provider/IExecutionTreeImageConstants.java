package org.key_project.sed.ui.visualization.execution_tree.provider;

import org.key_project.sed.core.model.ISEDBranchCondition;
import org.key_project.sed.core.model.ISEDBranchNode;
import org.key_project.sed.core.model.ISEDExceptionalTermination;
import org.key_project.sed.core.model.ISEDLoopCondition;
import org.key_project.sed.core.model.ISEDLoopNode;
import org.key_project.sed.core.model.ISEDMethodCall;
import org.key_project.sed.core.model.ISEDMethodReturn;
import org.key_project.sed.core.model.ISEDStatement;
import org.key_project.sed.core.model.ISEDTermination;
import org.key_project.sed.core.model.ISEDThread;

/**
 * <p>
 * This interface provides predefined image constants which can be used by the
 * features for image graphics algorithm.
 * </p>
 * <p>
 * Images itself are provided via {@link ExecutionTreeImageProvider} which
 * is instantiated and managed by Graphiti's extension points.
 * </p>
 * @author Martin Hentschel
 * @see ExecutionTreeImageProvider
 */
public interface IExecutionTreeImageConstants {
   /**
    * The constant prefix of all image keys.
    */
   public static final String PREFIX = "org.key_project.sed.ui.visualization.";
   
   /**
    * Key of the image for {@link ISEDBranchCondition}s.
    */
   public static final String IMG_BRANCH_CONDITION = PREFIX + "branchCondition";

   /**
    * Key of the image for {@link ISEDBranchNode}s.
    */
   public static final String IMG_BRANCH_NODE = PREFIX + "branchNode";

   /**
    * Key of the image for {@link ISEDExceptionalTermination}s.
    */
   public static final String IMG_EXCEPTIONAL_TERMINATION = PREFIX + "exceptionalTermination";

   /**
    * Key of the image for {@link ISEDLoopCondition}s.
    */
   public static final String IMG_LOOP_CONDITION = PREFIX + "loopCondition";

   /**
    * Key of the image for {@link ISEDLoopNode}s.
    */
   public static final String IMG_LOOP_NODE = PREFIX + "loopNode";

   /**
    * Key of the image for {@link ISEDMethodCall}s.
    */
   public static final String IMG_METHOD_CALL = PREFIX + "methodCall";

   /**
    * Key of the image for {@link ISEDMethodReturn}s.
    */
   public static final String IMG_METHOD_RETURN = PREFIX + "methodReturn";

   /**
    * Key of the image for {@link ISEDStatement}s.
    */
   public static final String IMG_STATEMENT = PREFIX + "statement";

   /**
    * Key of the image for {@link ISEDTermination}s.
    */
   public static final String IMG_TERMINATION = PREFIX + "termination";

   /**
    * Key of the image for {@link ISEDThread}s.
    */
   public static final String IMG_THREAD = PREFIX + "thread";
}
