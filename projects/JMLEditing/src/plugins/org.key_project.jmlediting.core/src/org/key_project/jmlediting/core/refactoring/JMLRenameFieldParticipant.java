package org.key_project.jmlediting.core.refactoring;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;

/**
 * Provides extended Rename Refactoring for Local Variables JML Comments.
 *
 * @author David Giessing
 *
 */
public class JMLRenameFieldParticipant extends RenameParticipant {

   @Override
   protected boolean initialize(final Object element) {
      // TODO Auto-generated method stub
      System.out.println("Element" + element);
      return true;
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
      return null;
   }

   @Override
   public Change createChange(final IProgressMonitor pm) throws CoreException,
         OperationCanceledException {
      System.out.println("Arguments " + this.getArguments());
      // TODO Auto-generated method stub
      return null;
   }
}