package org.key_project.jmlediting.profile.jmlref.refactoring.participants;

import java.util.ArrayList;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RefactoringUtil;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RenameRefactoringComputer;

/**
 * Class to participate in the renaming of classes.
 * <p>
 * Note that this participant uses {{@link #createPreChange(IProgressMonitor)} to avoid
 * synchronization problems. Any changes returned by this participant (that is, changes not
 * added to the scheduled java changes) are done before the java changes. This makes sure that
 * the compilation unit was not already renamed. Otherwise, an exception would be thrown
 * because the file system is not in sync anymore.
 * </p>
 * <p>
 * Note that the renaming of a class is not considered a text change.
 * </p>
 * 
 * @author Robert Heimbach
 *
 */
public class JMLRenameParticipantClass extends RenameParticipant {

   private IJavaElement fJavaElementToRename;
   private String fNewName;
   private String fOldName;
   private IJavaProject fProject; // the project which has the fields to be renamed

   /**
    * Name of this class.
    * <p>
    * {@inheritDoc}
    */
   @Override
   public final String getName() {
      return "JML Class Refactoring Rename Participant";
   }

   /**
    * Saves the new name to change to. Saves the old name and the class to be changed as a
    * {@link IJavaElement} to search for references to it. Saves the active Project, i.e. the
    * project which contains the renamed class.
    * <p>
    * {@inheritDoc}
    */
   @Override
   protected final boolean initialize(final Object element) {
      fNewName = getArguments().getNewName();
      fJavaElementToRename = (IJavaElement) element;
      fProject = fJavaElementToRename.getJavaProject();
      fOldName = fJavaElementToRename.getElementName();
      return true;
   }

   /**
    * Do nothing. Changes are done directly.
    * <p>
    * {@inheritDoc}
    */
   @Override
   public final RefactoringStatus checkConditions(final IProgressMonitor pm,
         final CheckConditionsContext context) throws OperationCanceledException {

      return new RefactoringStatus();
   }

   /**
    * Returns null. That is, no changes.
    * <p>
    * createPreChange is used instead to avoid synchronization problems.
    */
   @Override
   public final Change createChange(final IProgressMonitor pm) {
      return null;
   }

   /**
    * Computes the changes which need to be done to the JML code.
    * <p>
    * 
    * @return Returns null if only shared text changes are made. Otherwise returns a
    *         {@link TextChange} which gathered all the changes to JML annotations in classes
    *         which do not have any Java changes scheduled.
    *         </p>
    */
   @Override
   public final Change createPreChange(final IProgressMonitor pm) throws CoreException,
         OperationCanceledException {

      // Only non empty change objects will be added
      ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();

      RenameRefactoringComputer changesComputer = new RenameRefactoringComputer(
            fJavaElementToRename, fOldName, fNewName);

      // Find out the projects which need to be checked: active project plus all dependencies
      ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
      projectsToCheck.add(fProject);

      try {// Look through all source files in each package and project
         for (final IJavaProject project : RefactoringUtil.getAllProjectsToCheck(
               projectsToCheck, fProject)) {
            for (final IPackageFragment pac : RefactoringUtil
                  .getAllPackageFragmentsContainingSources(project)) {
               for (final ICompilationUnit unit : pac.getCompilationUnits()) {

                  final ArrayList<ReplaceEdit> changesToJML = changesComputer
                        .computeNeededChangesToJML(unit, project);

                  // Get scheduled changes to the java code from the rename processor
                  final TextChange changesToJavaCode = getTextChange(unit);

                  // add our edits to the java changes
                  // JDT will compute the shifts and the preview
                  if (changesToJavaCode != null) {
                     for (final ReplaceEdit edit : changesToJML) {
                        changesToJavaCode.addEdit(edit);
                     }
                  }
                  else {
                     // In case changes to the JML code needs to be done (but not to the java
                     // code)
                     if (!changesToJML.isEmpty()) {

                        changesToFilesWithoutJavaChanges.add(RefactoringUtil
                              .combineEditsToChange(unit, changesToJML));
                     }
                  }
               }
            }
         }
      }
      catch (final JavaModelException e) {
         return null;
      }

      // After iterating through all needed projects and source files, determine what needs to
      // be returned.
      return RefactoringUtil.assembleChangeObject(changesToFilesWithoutJavaChanges);
   }
}
