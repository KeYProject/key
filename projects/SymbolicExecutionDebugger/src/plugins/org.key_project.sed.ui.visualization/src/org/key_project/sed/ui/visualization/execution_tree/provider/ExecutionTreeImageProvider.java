package org.key_project.sed.ui.visualization.execution_tree.provider;

import org.eclipse.graphiti.ui.platform.AbstractImageProvider;
import org.eclipse.graphiti.ui.platform.IImageProvider;

/**
 * <p>
 * {@link IImageProvider} specific implementation for execution tree diagrams.
 * </p>
 * <p>
 * The constants of provided images are specified via interface {@link IExecutionTreeImageConstants}.
 * </p>
 * <p>
 * This class is instantiated an manged by Graphiti's extension points.
 * </p>
 * @author Martin Hentschel
 * @see IExecutionTreeImageConstants
 */
public class ExecutionTreeImageProvider extends AbstractImageProvider {
   /**
    * Path to the folder which contains the provided images.
    */
   private static final String ROOT_FOLDER_FOR_IMG = "icons/";

   /**
    * {@inheritDoc}
    */
   @Override
   protected void addAvailableImages() {
       addImageFilePath(IExecutionTreeImageConstants.IMG_BRANCH_CONDITION, ROOT_FOLDER_FOR_IMG + "branch_condition.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_BRANCH_NODE, ROOT_FOLDER_FOR_IMG + "branch_node.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_EXCEPTIONAL_TERMINATION, ROOT_FOLDER_FOR_IMG + "exceptional_termination.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_LOOP_CONDITION, ROOT_FOLDER_FOR_IMG + "loop_condition.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_LOOP_NODE, ROOT_FOLDER_FOR_IMG + "loop_node.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_METHOD_CALL, ROOT_FOLDER_FOR_IMG + "method_call.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_METHOD_RETURN, ROOT_FOLDER_FOR_IMG + "method_return.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_STATEMENT, ROOT_FOLDER_FOR_IMG + "statement.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_TERMINATION, ROOT_FOLDER_FOR_IMG + "termination.gif");
       addImageFilePath(IExecutionTreeImageConstants.IMG_THREAD, ROOT_FOLDER_FOR_IMG + "thread.gif");
   }
}