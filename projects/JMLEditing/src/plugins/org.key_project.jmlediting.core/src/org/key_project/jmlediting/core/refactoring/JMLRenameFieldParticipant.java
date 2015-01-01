package org.key_project.jmlediting.core.refactoring;

import java.util.HashMap;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.IField;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.key_project.util.jdt.JDTUtil;

/**
 * Provides extended Rename Refactoring for Local Variables JML Comments.
 *
 * @author David Giessing
 *
 */
public class JMLRenameFieldParticipant extends RenameParticipant {

   /**
    * initializes the RenameParticipant with the given element.
    *
    * @return true if element implements IField else returns false to not
    *         further be part of the refactoring
    */
   @Override
   protected boolean initialize(final Object element) {
      System.out.println("Element: " + element + "Type: " + element.getClass());
      for (final Class<?> c : element.getClass().getInterfaces()) {
         if (c.equals(IField.class)) {
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
      // TODO Auto-generated method stub
      return new RefactoringStatus();
   }

   @Override
   public Change createChange(final IProgressMonitor pm) throws CoreException,
         OperationCanceledException {
      System.out.println("Arguments: " + this.getArguments());
      final HashMap changes;
      final String newName = this.getArguments().getNewName();
      final ASTNode parseResult = JDTUtil
            .parse(compilationUnit, offset, length);
      // TODO Auto-generated method stub
      return null;
   }

}