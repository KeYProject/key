package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;

/**
 * The refactoring computer to compute changes to the JML annotations when a renaming was done by
 * calling the method {@link #computeNeededChangesToJML(ICompilationUnit, IJavaProject)}.
 * <p>
 * The list of {@link IStringNode}s is filtered by comparing the Strings to the name of the element
 * which is refactored. Filtering is important to reduce the number of times the Resolver is called.
 * </p>
 * <p>
 * The {@link ReplaceEdit}s are created by calling the {@link Resolver} and finding out if the JML
 * expression / the {@link IASTNode} refers to the element to be refactored. Complex expressions
 * need to call the {@link Resolver#next()} method which traverses the tree structure.
 * </p>
 * 
 * @author Robert Heimbach
 * 
 * @see {@link AbstractRefactoringComputer}
 */
public class RenameRefactoringComputer extends AbstractRefactoringComputer {

   private Object fOldName;
   private Object fJavaElementToRename;
   private String fNewName;

   /**
    * Constructor of the rename refactoring computer. Additionally to the old and new name of the
    * element to be renamed it saves a reference to the element itself to check later which elements
    * in the JML annotations really refer to this element.
    * 
    * @param fJavaElementToRename
    *           Element which is renamed.
    * @param fOldName
    *           Old name of the element which is renamed.
    * @param fNewName
    *           New name of the element which is renamed.
    */
   public RenameRefactoringComputer(IJavaElement fJavaElementToRename, String fOldName,
         String fNewName) {
      this.fOldName = fOldName;
      this.fNewName = fNewName;
      this.fJavaElementToRename = fJavaElementToRename;
   }

   /**
    * Filters a list of {@link IASTNode} for those which potentially reference the element to be
    * renamed by comparing the string node to the old name of the element to be renamed.
    * 
    * @param nodesList
    *           List to filter. Should be a list of {@link IStringNode}s.
    * @return filtered list of string nodes. Potentially empty.
    */
   protected final ArrayList<IStringNode> filterStringNodes(final List<IASTNode> nodesList) {

      final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();

      for (final IASTNode node : nodesList) {
         final IStringNode stringNode = (IStringNode) node;
         if (stringNode.getString().equals(fOldName)) {
            filteredList.add(stringNode);
         }
      }

      return filteredList;
   }

   /**
    * Checks if a given {@link IASTNode} in a given {@link ICompilationUnit} references the element
    * to be renamed. Then the needed {@Link ReplaceEdit} is created and added to
    * changesToMake.
    *
    * @param unit
    *           The compilation unit the IASTNode is in.
    * @param changesToMake
    *           {@link ArrayList} of {@link ReplaceEdit}s to accumulate the needed changes.
    * @param primaryStringMap
    *           {@link HashMap} which provides for all primary node which needs to be resolved a
    *           list of {@link IStringNode}s which all had this node as their primary.
    */
   @Override
   protected final void computeReplaceEdit(final ICompilationUnit unit,
         final ArrayList<ReplaceEdit> changesToMake,
         final HashMap<IASTNode, List<IStringNode>> primaryStringMap) {

      // Get the resolver which is defined for the active profile.
      IResolver resolver = JMLPreferencesHelper.getProjectActiveJMLProfile(
            unit.getJavaProject().getProject()).getResolver();

      try {

         for (IASTNode primary : primaryStringMap.keySet()) {

            List<IStringNode> stringNodes = primaryStringMap.get(primary);

            boolean changeNeeded = false;

            // only one stringNode --> Resolve the whole primary
            // change the position given by the IStringNode
            if (stringNodes.size() == 1) {

               changeNeeded = isReferencedElement(resolver.resolve(unit, primary));

               // complex primaries need more calls to the resolver
               while (changeNeeded == false && resolver.hasNext()) {
                  changeNeeded = isReferencedElement(resolver.next());
               }

               if (changeNeeded) {
                  createEditAndAddToList(changesToMake, stringNodes.get(0));
               }
            }
            else {// Shared primaries. Several string nodes had this node as their primary.
                  // the resolver provides the information which part of the node needs to be
                  // changed.

               ResolveResult result = null;

               result = resolver.resolve(unit, primary);

               if (isReferencedElement(result)) {
                  createEditAndAddToList(changesToMake, result.getStringNode());
               }

               while (resolver.hasNext()) {

                  result = resolver.next();

                  if (isReferencedElement(result)) {
                     createEditAndAddToList(changesToMake, result.getStringNode());
                  }
               }
            }
         }
      }
      catch (ResolverException e) {
         LogUtil.getLogger().logError(e);
         ;
      }
   }

   /**
    * Checks if the resolved result equals the element to be renamed.
    * 
    * @param result
    *           The {@link ResolveResult}.
    * @return true if the resolve result equals the element to be renamed. Falls otherwise.
    */
   private Boolean isReferencedElement(final ResolveResult result) {
      if (result == null || result.getBinding() == null) {
         return false;
      }
      else
         return result.getBinding().getJavaElement().equals(fJavaElementToRename);
   }

   /**
    * Creates the text change and adds it to changesToMake.
    * 
    * @param changesToMake
    *           list of {@link ReplaceEdit}s to fill.
    * @param node
    *           the {@link IASTNode} which should be edited.
    */
   private void createEditAndAddToList(final ArrayList<ReplaceEdit> changesToMake,
         final IStringNode node) {

      // compute the text location which needs to change.
      final int startOffset = node.getStartOffset();
      final int length = node.getEndOffset() - node.getStartOffset();

      final ReplaceEdit edit = new ReplaceEdit(startOffset, length, fNewName);

      changesToMake.add(edit);
   }
}
