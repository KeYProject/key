package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.profile.syntax.IKeywordContentRefactorer;
import org.key_project.jmlediting.core.utilities.JavaElementIdentifier;

/**
 * provides a Method to create changes needed for a Rename Refactoring in
 * StoreRefKeywords.
 *
 * @author David Giessing
 *
 */
public class StoreRefKeywordRefactorer implements IKeywordContentRefactorer {

   /**
    * The Compilation Unit in which the refactoring has to be done.
    */
   private ICompilationUnit cu;
   /**
    * the source of the CompilationUnit.
    */
   private String src;
   /**
    * The unique identifier for the Element that has to be refactored.
    */
   private JavaElementIdentifier elem;

   @Override
   public Change refactorFieldRename(final JavaElementIdentifier elem,
         final IASTNode contentNode, final ICompilationUnit cu) {
      this.cu = cu;
      IResource res = null;
      final CompositeChange change = new CompositeChange(elem.getName()
            + " renaming");
      try {
         res = cu.getCorrespondingResource();
         if (res.getType() == IResource.FILE) {
            System.out.println("isFile");
            final IFile file = (IFile) res;
         }
      }
      catch (final JavaModelException e) {
         /*
          * If no IFile can be retrieved from cu, no refactoring can be provided
          * since we can not create Changes
          */
         System.out.println("Compilation Unit was no File ");
         return null;
      }

      this.elem = elem;
      try {
         this.src = cu.getSource();
      }
      catch (final JavaModelException e1) {
         System.out.println("Could not get SourceCode");
         return null;
      }
      final List<Change> changes = Collections.emptyList();
      System.out.println(contentNode.prettyPrintAST() + " "
            + contentNode.getChildren().size());
      for (final IASTNode node : contentNode.getChildren()) {
         if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME) {
            System.out.println("StoreRefName");
            // TODO: something
            if (this.src.substring(node.getStartOffset(), node.getEndOffset())
                  .matches(elem.getName())) {
               System.out.println("Found match in StoreRefName");
            }
         }
         else if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME_SUFFIX) {
            System.out.println("StoreRefNameSuffix");
            // TODO: do something else
            if (this.src.substring(node.getStartOffset(), node.getEndOffset())
                  .matches(elem.getName())) {
               System.out.println("Found match in StoreRefNameSuffix");

            }
         }
         else {
            System.out.println("Going Deeper");
            change.add(this.refactorFieldRenameRecursively(node));
         }
      }

      return change;
   }

   /**
    * Traverses the AST and compiles a List of Changes.
    *
    * @param contentNode
    *           the actual Content Node
    * @return a List of Changes
    */
   private Change refactorFieldRenameRecursively(final IASTNode contentNode) {
      final CompositeChange change = new CompositeChange(this.elem.getName());
      for (final IASTNode node : contentNode.getChildren()) {
         if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME) {
            System.out.println("StoreRefName Recursively");
            // TODO: something
            if (this.src.substring(node.getStartOffset(), node.getEndOffset())
                  .matches(this.elem.getName())) {
               System.out.println("Found match in StoreRefName Recursively");
            }
         }
         else if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME_SUFFIX) {
            System.out.println("StoreRefNameSuffix Recursively");
            // TODO: do something else
            if (this.src.substring(node.getStartOffset(), node.getEndOffset())
                  .matches(this.elem.getName())) {
               System.out
                     .println("Found match in StoreRefNameSuffix Recursively");
            }
         }
         else {
            System.out.println("Going Deeper Recursively");
            change.add((this.refactorFieldRenameRecursively(node)));
         }
      }

      return change;
   }
}
