package org.key_project.jmlediting.profile.jmlref.refactoring.participants;

import java.util.ArrayList;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.MoveParticipant;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.FieldAndMethodMoveRefactoringComputer;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RefactoringUtil;

/**
 * Class to participate in the move refactoring of static fields and methods.
 * 
 * @author Maksim Melnik, Robert Heimbach
 */
public class JMLMoveParticipantSFieldAndMethod extends MoveParticipant {

   private String elementName;

   private String oldClassFullQualName; // fully qualified name of the old class
   private String newClassFullQualName;
   private IJavaProject fProject;

   /**
    * {@inheritDoc} Saves the element which is moved, the name of the element, its source and
    * destination class, as well as the project starting the refactoring.
    */
   @Override
   protected final boolean initialize(Object element) {
      IJavaElement elementToMove = (IJavaElement) element;
      fProject = elementToMove.getJavaProject();
      elementName = elementToMove.getElementName();
      oldClassFullQualName = ((IType) elementToMove.getParent()).getFullyQualifiedName();
      IType destination = (IType) getArguments().getDestination();
      newClassFullQualName = destination.getFullyQualifiedName();
      return true;
   }

   /**
    * Name of this class.
    * <p>
    * {@inheritDoc}
    */
   @Override
   public final String getName() {
      return "JML Field and Method Move Participant";
   }

   /**
    * Do nothing.
    * <p>
    * {@inheritDoc}
    */
   @Override
   public final RefactoringStatus checkConditions(IProgressMonitor pm,
         CheckConditionsContext context) throws OperationCanceledException {
      return new RefactoringStatus();
   }

   /**
    * Computes the changes which need to be done to the JML code.
    * <p>
    * However, first all already scheduled changes to the java source code need to be
    * performed. Otherwise the basis for computing the JML changes would have been outdated
    * and thus changes to regions which are moved together with the element would have been
    * scheduled in the old file where the deletion is happening and not in the new file where
    * the insertion is happening. Also regions with changes are very large in the change tree
    * when elements are moved and no additional changes working on these regions are allowed
    * to be added.
    * 
    * @return Returns null if no changes to any JML annotations are made. Otherwise, a
    *         {@link TextChange} is returned describing the changes which needs to be done to
    *         the JML annotations.
    *
    */
   @Override
   public final Change createChange(IProgressMonitor pm) throws CoreException,
         OperationCanceledException {

      // Only non empty change objects will be added
      ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();

      // Find out the projects which need to be checked: active project plus all dependencies
      ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
      projectsToCheck.add(fProject);

      try {
         // Look through all source files in each package and project and perform the
         // scheduled java changes, if available.
         for (final IJavaProject project : RefactoringUtil.getAllProjectsToCheck(
               projectsToCheck, fProject)) {
            for (final IPackageFragment pac : RefactoringUtil
                  .getAllPackageFragmentsContainingSources(project)) {
               for (final ICompilationUnit unit : pac.getCompilationUnits()) {

                  final TextChange changesToJavaCode = getTextChange(unit);

                  if (changesToJavaCode != null) {
                     changesToJavaCode.perform(pm);
                     changesToJavaCode.dispose();
                  }
               }
            }
         }

         // Now check the updated files for needed JML changes. We could not have done it
         // before, because import declarations needed to be updated.
         for (final IJavaProject project : RefactoringUtil.getAllProjectsToCheck(
               projectsToCheck, fProject)) {
            for (final IPackageFragment pac : RefactoringUtil
                  .getAllPackageFragmentsContainingSources(project)) {
               for (final ICompilationUnit unit : pac.getCompilationUnits()) {

                  FieldAndMethodMoveRefactoringComputer changesComputer = new FieldAndMethodMoveRefactoringComputer(
                        oldClassFullQualName, newClassFullQualName, elementName, unit);

                  ArrayList<ReplaceEdit> changesToJML = changesComputer
                        .computeNeededChangesToJML(unit, project);

                  if (!changesToJML.isEmpty()) {
                     changesToFilesWithoutJavaChanges.add(RefactoringUtil
                           .combineEditsToChange(unit, changesToJML));
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
