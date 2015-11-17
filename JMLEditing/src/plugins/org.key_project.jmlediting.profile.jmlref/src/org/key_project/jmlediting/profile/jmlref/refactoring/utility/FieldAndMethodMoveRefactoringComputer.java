package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * Class to compute the changes which needs to be done to the JML annotations if a static
 * field or method is moved. In particular, it specifies how the list of nodes is filtered,
 * i.e. how the JML expression to be replaced is found.
 * <p>
 * Note that {@link #filterStringNodes(List)} in this class is considerably more complex than
 * in {@link ClassMoveRefactoringComputer} because static fields and methods can be accessed
 * in a non fully qualified way, i.e. Classname.elementToMove, additionally to the fully qualified way
 * of package.subpackage.Classname.elementToMove.
 * </p>
 * 
 * @author Robert Heimbach, Maksim Melnik
 *
 */
public class FieldAndMethodMoveRefactoringComputer extends AbstractRefactoringComputer {

   private String elementName;
   private String oldClassFullQualName;
   private String newClassFullQualName;
   private ICompilationUnit compUnit;

   /**
    * Constructor, which saves the fully qualified name of the classes the field/method should
    * be moved from and moved to as well as the name of the field/method to be moved and the
    * compilation unit for which the JML changes should be computed for.
    * 
    * @param oldClassFullQualName Fully qualified name of the class the field/method is in.
    * @param newClassFullQualName Fully qualified name of the class the field/method should be
    *           moved to.
    * @param elementName Name of the field/method to be moved.
    * @param unit {@link ICompilationUnit} for which the changes are computed for.
    */
   public FieldAndMethodMoveRefactoringComputer(String oldClassFullQualName,
         String newClassFullQualName, String elementName, ICompilationUnit unit) {
      this.oldClassFullQualName = oldClassFullQualName;
      this.newClassFullQualName = newClassFullQualName;
      this.elementName = elementName;
      this.compUnit = unit;
   }

   /**
    * Filters a list of {@link IASTNode} to exclude JML expressions which does not need to be
    * changed. First, all fully qualified references are searched and then the non fully
    * qualified ones.
    * 
    * @param nodesList a list to be filtered. {@link IStringNode}s are expected.
    * @return list of filtered {@link IStringNode}s.
    */
   protected final List<IStringNode> filterStringNodes(List<IASTNode> nodesList) {
      final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
      String nodeString = "";

      // Note that StringNodes are single words or even dots. They need to be combined.
      // Search for fully qualified references
      for (final IASTNode node : nodesList) {
         final IStringNode stringNode = (IStringNode) node;

         // sequentially, add string nodes as long as it could be a fully qualified reference
         if ((oldClassFullQualName + "." + elementName).contains(stringNode.getString()))
            nodeString = nodeString + stringNode.getString();
         // reset
         else
            nodeString = "";

         if (nodeString.equals(oldClassFullQualName + "." + elementName)) {
            filteredList.add(stringNode);
         }
      }

      // Check for non fully qualified access, that is OldClassName.elementName
      // Only needed in certain cases.
      if (checkForNonFullyQualified()) {

         String oldClassName = oldClassFullQualName.substring(oldClassFullQualName
               .lastIndexOf('.') + 1);
         nodeString = "";

         for (final IASTNode node : nodesList) {
            final IStringNode stringNode = (IStringNode) node;

            // combine the string nodes
            if ((oldClassName + "." + elementName).contains(stringNode.getString()))
               nodeString = nodeString + stringNode.getString();
            // reset
            else
               nodeString = "";

            if (nodeString.equals(oldClassName + "." + elementName)) {
               // Note that the nodeString will start to accumulate with a dot in case it
               // is in fact a fully qualified reference and thus will never be equal to
               // OldClass.fieldToMove
               filteredList.add(stringNode);
            }
         }
      }

      return filteredList;
   }

   /**
    * Check if it is needed to check for non fully qualified access to static methods or
    * fields. Possible if : 1) We are in the class we moved the field to (e.g. if an invariant
    * was moved with it) 2) The destination class of the element to be moved is imported by or
    * in the same package as the class for which the JML changes are computed.
    * 
    * @return true if non fully qualified access, i.e. ClassName.field, is possible.
    */
   private boolean checkForNonFullyQualified() {

      int lastPoint = newClassFullQualName.lastIndexOf('.');
      
      String packageNewClass;
      String newClassName;
      
      // Check if the destination package is the default package
      if (lastPoint == -1) {
         packageNewClass = "";
         newClassName = newClassFullQualName;
      }
      else {
         packageNewClass = newClassFullQualName.substring(0, lastPoint);
         newClassName = newClassFullQualName.substring(lastPoint + 1);
      }


      // Check if we want to compute JML changes for the destination class
      String nameOfCurrentClass = compUnit.getElementName().substring(0,
            compUnit.getElementName().lastIndexOf('.'));
      if (nameOfCurrentClass.equals(newClassName)) {
         return true;
      }

      // Non fully qualified references are possible if the destination class with the field
      // being
      // moved is imported
      if (compUnit.getImport(newClassFullQualName).exists())
         return true;

      // check if the package of the destination class is imported using a wildcard/on demand
      // import
      // Note that a class in the package of the current compilation unit with the same name
      // as the
      // destination class
      // has a higher priority than the wildcard import and would be used instead.
      if (compUnit.getImport(packageNewClass + ".*").exists()) {
         try {
            IJavaElement[] elementsInCUPackage = ((IPackageFragment) compUnit.getParent())
                  .getChildren();
            for (IJavaElement ele : elementsInCUPackage) {
               if (ele.getElementType() == IJavaElement.COMPILATION_UNIT) {
                  String elementName = ele.getElementName();
                  // remove the .java from Classname.java
                  String className = elementName.substring(0, elementName.lastIndexOf('.'));
                  if (className.equals(newClassName))
                     return false;
               }
            }
            // we have not found any class with the same name as the destination class
            return true;
         }
         catch (JavaModelException e) {
            return false;
         }
      }

      return false;
   }

   /**
    * Creates the text change and adds it to {@code changesToMake}. It is important to 
    * distinguish whether a fully qualified reference is done or not.
    * 
    * @param unit not needed here.
    * @param changesToMake list to add the {@link ReplaceEdit}s to.
    * @param primaryStringMap {@link IASTNode} to compute the change for and the
    *           {@link IStringNode}s which they contain.
    */
   protected final void computeReplaceEdit(ICompilationUnit unit,
         ArrayList<ReplaceEdit> changesToMake,
         HashMap<IASTNode, List<IStringNode>> primaryStringMap) {

      for (IASTNode node : primaryStringMap.keySet()) {

         final int startOffset = node.getStartOffset();

         String newClassName = newClassFullQualName.substring(newClassFullQualName
               .lastIndexOf('.') + 1);
         String oldClassName = oldClassFullQualName.substring(oldClassFullQualName
               .lastIndexOf('.') + 1);

         // check which type of access it is. The type determines the length of the replace
         // edit and the new content.
         // Non fully qualified access starts with the class name instead of the package name.
         IASTNode innerNode = node.getChildren().get(0).getChildren().get(0);
         if (innerNode instanceof IStringNode
               && ((IStringNode) innerNode).getString().equals(oldClassName)) {
            changesToMake.add(new ReplaceEdit(startOffset, oldClassName.length(),
                  newClassName));
         }
         else {
            final int length = oldClassFullQualName.length();
            changesToMake.add(new ReplaceEdit(startOffset, length, newClassFullQualName));
         }
      }
   }
}
