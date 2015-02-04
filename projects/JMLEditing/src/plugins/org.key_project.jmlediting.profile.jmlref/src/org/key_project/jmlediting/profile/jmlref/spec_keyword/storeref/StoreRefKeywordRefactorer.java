package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import java.util.Collections;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ltk.core.refactoring.Change;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.profile.syntax.IKeywordContentRefactorer;
import org.key_project.jmlediting.core.utilities.JavaElementIdentifier;

public class StoreRefKeywordRefactorer implements IKeywordContentRefactorer {

   private ICompilationUnit cu;
   private String src;
   private JavaElementIdentifier elem;

   public StoreRefKeywordRefactorer() {
      // TODO Auto-generated constructor stub
   }

   @Override
   public List<Change> refactorFieldRename(final JavaElementIdentifier elem,
         final IASTNode contentNode, final ICompilationUnit cu) {
      this.cu = cu;
      this.elem = elem;
      try {
         this.src = cu.getSource();
      }
      catch (final JavaModelException e1) {
         // TODO Auto-generated catch block
         e1.printStackTrace();
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
            changes.addAll(this.refactorFieldRenameRecursively(node));
         }
      }

      return changes;
   }

   private List<Change> refactorFieldRenameRecursively(
         final IASTNode contentNode) {
      final List<Change> changes = Collections.emptyList();
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
            changes.addAll(this.refactorFieldRenameRecursively(node));
         }
      }

      return changes;
   }
}
