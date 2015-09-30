package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * Class to compute the changes which needs to be done to the JML annotations if a class is
 * moved. In particular, it specifies how the list of nodes is filtered, i.e. how the JML
 * expression to be replaced is found.
 * 
 * @author Maksim Melnik, Robert Heimbach
 *
 */
public class ClassMoveRefactoringComputer extends AbstractRefactoringComputer {

   private final String fOldFullQualName;
   private final String fOldPackName;
   private final String fNewPackName;

   /**
    * Constructor, which saves the fully qualified name of the class which is moved and the
    * source package the class is in and the destination package it should be moved to.
    * 
    * @param fOldPackName name of the package the class is in.
    * @param fNewPackName name of the package the class should be moved to.
    * @param fOldFullQualName fully qualified name / path of the class to be moved.
    */
   public ClassMoveRefactoringComputer(final String fOldPackName, final String fNewPackName,
         final String fOldFullQualName) {
      this.fOldPackName = fOldPackName;
      this.fNewPackName = fNewPackName;
      this.fOldFullQualName = fOldFullQualName;
   }

   /**
    * Filters a list of {@link IASTNode} to exclude JML expression which does not need to be
    * changed.
    * 
    * @param nodesList a list to be filtered. {@link IStringNode}s are expected.
    * @return list of filtered {@link IStringNode}s.
    */
   @Override
   protected final List<IStringNode> filterStringNodes(final List<IASTNode> nodesList) {
      final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();

      // Note that an expression like package.subpackage.Class is separated in three nodes.

      // To combine the expression
      String nodeString = "";

      for (final IASTNode node : nodesList) {
         final IStringNode stringNode = (IStringNode) node;

         // combine the expression because the current String is contained in the string to
         // replace.
         if (fOldFullQualName.contains(stringNode.getString())) {
            nodeString = nodeString + stringNode.getString();
         // reset the expression
         } else {
            nodeString = "";
         }

         if (nodeString.equals(fOldFullQualName)) {
            filteredList.add(stringNode);
         }
      }
      return filteredList;
   }

   /**
    * Creates the text change and adds it to {@code changesToMake}.
    * 
    * @param unit not needed here.
    * @param changesToMake list to add the {@link ReplaceEdit}s to.
    * @param primaryStringMap {@link IASTNode} to compute the change for and the
    *           {@link IStringNode}s which they contain.
    */
   @Override
   protected final void computeReplaceEdit(final ICompilationUnit unit,
         final ArrayList<ReplaceEdit> changesToMake,
         final HashMap<IASTNode, List<IStringNode>> primaryStringMap) {

      for (final IASTNode node : primaryStringMap.keySet()) {

         final int startOffset = node.getStartOffset();

         int length = fOldPackName.length();
         
//         if (length == 0) {
//            // was in default package before. Needs to add a dot.
//            fNewPackName = fNewPackName + ".";
//            //length = length + 1;
//         }
         
         // if the destination is the default package, we need to replace the dot too
         if (fNewPackName.equals("")){
            length = length + 1;
         }
         
         changesToMake.add(new ReplaceEdit(startOffset, length, fNewPackName));
      }
   }
}