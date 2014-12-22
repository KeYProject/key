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
public class JMLRenameFieldProcessor extends RenameParticipant {

   @Override
   protected boolean initialize(final Object element) {
      // TODO Auto-generated method stub
      return false;
   }

   @Override
   public String getName() {
      // TODO Auto-generated method stub
      return null;
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
      // TODO Auto-generated method stub
      return null;
   }

}