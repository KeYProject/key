package org.key_project.jmlediting.core.refactoring;

import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.ui.SharedASTProvider;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.key_project.jmlediting.core.utilities.JMLJavaResolver;
import org.key_project.jmlediting.core.utilities.JavaElementIdentifier;
import org.key_project.jmlediting.core.utilities.Range;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;

/**
 * Provides extended Rename Refactoring for Local Variables JML Comments.
 *
 * @author David Giessing
 *
 */
public class JMLRenameFieldParticipant extends RenameParticipant {

   /**
    * The element that shall be refactored.
    */
   private Object element;

   /**
    * initializes the RenameParticipant with the given element.
    *
    * @return true if element implements IField else returns false to not
    *         further be part of the refactoring
    */
   @Override
   protected boolean initialize(final Object element) {

      for (final Class<?> c : element.getClass().getInterfaces()) {
         if (c.equals(IField.class)) {
            this.element = element;
            // TODO: Activate
            return true;
         }
      }
      return false;
   }

   @Override
   public String getName() {
      return "JMLRenameFieldParticipant";
   }

   @Override
   public RefactoringStatus checkConditions(final IProgressMonitor pm,
         final CheckConditionsContext context)
         throws OperationCanceledException {
      return new RefactoringStatus();
   }

   @Override
   public Change createChange(final IProgressMonitor pm) throws CoreException,
         OperationCanceledException {
      // Cast Safe because of the Check in InitializerMethod
      final IField elem = (IField) this.element;
      final org.eclipse.jdt.core.dom.CompilationUnit cu = SharedASTProvider
            .getAST(elem.getCompilationUnit(), SharedASTProvider.WAIT_YES, null);
      final TypeDeclarationFinder finder = new TypeDeclarationFinder();
      cu.accept(finder);
      final List<TypeDeclaration> decls = finder.getDecls();
      final TypeDeclaration topDecl = decls.get(0);
      System.out.println(topDecl.resolveBinding().getName());
      final JMLJavaResolver resolver = JMLJavaResolver.getInstance(
            topDecl.resolveBinding(), true);
      final JavaElementIdentifier refGoal = new JavaElementIdentifier(
            elem.getElementName(), resolver.getTypeForName(elem
                  .getElementName()), elem.getDeclaringType());

      // final ReplaceEdit edit = new ReplaceEdit(offset,
      // refGoal.getName().length(), this
      // .getArguments().getNewName());
      return null;
   }

   /**
    * finds all occurences of the element that has to be refactored.
    *
    * @return a Range Array that contains all occurences of the Keyword. NULL if
    *         no occurences were found.
    */
   public Range[] getJMLOccurences() {
      return null;
   }
}