package org.key_project.jmlediting.profile.jmlref.refactoring.participants;

import java.util.ArrayList;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.ILocalVariable;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RenameRefactoringComputer;

/**
 * Participant to take part in the renaming of method parameters.
 * <p>
 * As the scope of method parameters is just the method itself, any JML annotation using the
 * renamed method parameter only makes sense above that particular method. Thus this
 * participant, unlike the others, only needs to check the active class for changes to make.
 * </p>
 * <p>
 * The class uses the {@link RenameRefactoringComputer} to compute the needed changes.
 * </p>
 * 
 * @author Robert Heimbach
 *
 */
public class JMLRenameParticipantParameters extends RenameParticipant {

   private String fNewName;
   private String fOldName;
   private ICompilationUnit fCompUnit;
   private ILocalVariable fmethodParameter;
   private IJavaProject fProject;

   /**
    * Initializes the refactoring participant with the needed information.
    * <p>
    * {@inheritDoc}
    */
   @Override
   protected final boolean initialize(final Object element) {
      if (!JMLPreferencesHelper.isExtensionEnabled()) {
         return false;
      }
      
      fmethodParameter = (ILocalVariable) element;

      // check if it is a method parameter
//      if (fmethodParameter.isParameter()) {
         fOldName = fmethodParameter.getElementName();
         fNewName = getArguments().getNewName();
         fProject = fmethodParameter.getJavaProject();
         fCompUnit = fmethodParameter.getDeclaringMember().getCompilationUnit();

         return true;
//      }
//      else {
//         return false;
//      }
   }

   /**
    * Name of this participant.
    * <p>
    * {@inheritDoc}
    */
   @Override
   public final String getName() {
      return "JML Parameters Refactoring Rename Participant";
   }

   /**
    * No condition checking. Changes are done directly (or not at all).
    * <p>
    * {@inheritDoc}
    */
   @Override
   public final RefactoringStatus checkConditions(final IProgressMonitor pm,
         final CheckConditionsContext context) throws OperationCanceledException {

      return new RefactoringStatus();
   }

   /**
    * Computes the changes which need to be done to the JML code of the active class and add
    * those to the changes to the java code which are already scheduled. Note that those
    * certainly exist, because the method using the parameter is in the active class.
    * 
    * @return Returns null, since changes to JML are directly added to the already scheduled
    *         java changes.
    */
   @Override
   public final Change createChange(final IProgressMonitor pm) throws CoreException, OperationCanceledException {
      if (!JMLPreferencesHelper.isExtensionEnabled()) {
         return null;
      }

      final RenameRefactoringComputer changesComputer = new RenameRefactoringComputer(
            fmethodParameter, fOldName, fNewName);

      final ArrayList<ReplaceEdit> changesToJML = changesComputer.computeNeededChangesToJML(
            fCompUnit, fProject);

      // Get scheduled changes to the java code from the rename processor
      final TextChange changesToJavaCode = getTextChange(fCompUnit);

      // add our edits to the java changes
      // JDT will compute the shifts and the preview
      for (final ReplaceEdit edit : changesToJML) {
         changesToJavaCode.addEdit(edit);
      }

      return null;
   }
}
