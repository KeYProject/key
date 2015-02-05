package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.profile.syntax.IKeywordContentRefactorer;
import org.key_project.jmlediting.core.utilities.ChangeShiftContainer;
import org.key_project.jmlediting.core.utilities.JavaRefactoringElementInformationContainer;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;

/**
 * provides a Method to create changes needed for a Rename Refactoring in
 * StoreRefKeywords. <br>
 * Code is following this <a href=
 * "http://alvinalexander.com/java/jwarehouse/eclipse/org.eclipse.jdt.ui.tests/examples/org/eclipse/jdt/ui/examples/MyRenameTypeParticipant.java.shtml"
 * > Example </a>
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
   private JavaRefactoringElementInformationContainer elem;
   /**
    * The file that is modified.
    */
   private IFile file;

   private int shift = 0;

   private int difference;

   @Override
   public ChangeShiftContainer refactorFieldRename(
         final JavaRefactoringElementInformationContainer elem,
         final IASTNode contentNode, final ICompilationUnit cu,
         final String srcAfterChanges, final int initialShift) {
      this.difference = elem.getNewName().length() - elem.getName().length();
      this.shift = initialShift;
      this.cu = cu;
      IResource res = null;
      final MultiTextEdit edits = new MultiTextEdit();
      TextFileChange tfchange = null;
      try {
         res = cu.getCorrespondingResource();
         if (res.getType() == IResource.FILE) {
            System.out.println("isFile");
            this.file = (IFile) res;
            tfchange = new TextFileChange("StoreRefNameEdit", this.file);
            tfchange.setEdit(edits);
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
      this.src = srcAfterChanges;
      System.out.println(contentNode.prettyPrintAST() + " "
            + contentNode.getChildren().size());
      for (final IASTNode node : contentNode.getChildren()) {
         if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME) {
            System.out.println("StoreRefName");
            // TODO: something
            if (this.src.substring(node.getStartOffset(), node.getEndOffset())
                  .equals(elem.getName())) {
               System.out.println("Found match in StoreRefName");
               final ReplaceEdit edit = new ReplaceEdit(node.getStartOffset()
                     + this.shift, node.getEndOffset() - node.getStartOffset(),
                     elem.getNewName());
               this.shift += this.difference;
               edits.addChild(edit);
            }
         }
         else if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME_SUFFIX) {
            // TODO: do something else
            if (this.src.substring(node.getStartOffset(), node.getEndOffset())
                  .equals(elem.getName())) {
               System.out.println("Found match in StoreRefNameSuffix");
               final ReplaceEdit edit = new ReplaceEdit(node.getStartOffset()
                     + this.shift, node.getEndOffset() - node.getStartOffset(),
                     elem.getNewName());
               this.shift += this.difference;
               edits.addChild(edit);
            }
         }
         else {
            System.out.println("Going Deeper");
            final Collection<ReplaceEdit> recursiveEdits = this
                  .refactorFieldRenameRecursively(node);
            for (final ReplaceEdit r : recursiveEdits) {
               edits.addChild(r);
            }
         }
      }
      return new ChangeShiftContainer(tfchange, this.shift);
   }

   /**
    * Traverses the AST and compiles a List of Changes.
    *
    * @param contentNode
    *           the actual Content Node
    * @return a List of Changes
    */
   private Collection<ReplaceEdit> refactorFieldRenameRecursively(
         final IASTNode contentNode) {
      final List<ReplaceEdit> changes = new ArrayList<ReplaceEdit>();
      for (final IASTNode node : contentNode.getChildren()) {
         if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME) {
            System.out.println("StoreRefName Recursively");
            // TODO: something
            if (this.src.substring(node.getStartOffset(), node.getEndOffset())
                  .equals(this.elem.getName())) {
               System.out.println("Found match in StoreRefName Recursively");
               final ReplaceEdit edit = new ReplaceEdit(node.getStartOffset()
                     + this.shift, node.getEndOffset() - node.getStartOffset(),
                     this.elem.getNewName());
               this.shift += this.difference;
               changes.add(edit);
            }
         }
         else if (node.getType() == StoreRefNodeTypes.STORE_REF_NAME_SUFFIX) {
            System.out.println("StoreRefNameSuffix Recursively");
            // TODO: do something else
            if (node.getChildren().get(0).getType() == ExpressionNodeTypes.IDENTIFIER) {
               System.out.println("Identifier: " + node.getChildren().get(0));
            }
            if (this.src.substring(node.getStartOffset(), node.getEndOffset())
                  .equals(this.elem.getName())) {
               System.out
               .println("Found match in StoreRefNameSuffix Recursively");
               final ReplaceEdit edit = new ReplaceEdit(node.getStartOffset()
                     + this.shift, node.getEndOffset() - node.getStartOffset(),
                     this.elem.getNewName());
               this.shift += this.difference;
               changes.add(edit);
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
