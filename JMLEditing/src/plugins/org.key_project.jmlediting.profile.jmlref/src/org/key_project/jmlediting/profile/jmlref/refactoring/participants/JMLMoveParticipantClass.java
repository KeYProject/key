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
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.ClassMoveRefactoringComputer;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RefactoringUtil;

/**
 * Class to participate in the move refactoring of java classes.
 * 
 * @author Maksim Melnik, Robert Heimbach
 */
public class JMLMoveParticipantClass extends MoveParticipant {
    private IJavaElement fToMove;        // file

    private String fDocName;                // file name

    private String fOldFullQualName;        // old fully qualified
    private String fOldPackName;            // old package name
    private String fNewPackName;            // new package name

    private IJavaProject fProject;

    /**
     * Initializes the source and destination paths, as well as the file to move itself.
     * <p>
     * {@inheritDoc} 
     */
    @Override
    protected final boolean initialize(Object element) {
        fToMove=(IJavaElement) element;

        fDocName = fToMove.getElementName();
        fOldFullQualName=((IType) element).getFullyQualifiedName();

        fProject = fToMove.getJavaProject();
        
        // get the old and new package name , because we only want to replace package names, otherwise nested classes problem        
        fOldPackName = fOldFullQualName.substring(0, fOldFullQualName.indexOf(fDocName)-1);
        fNewPackName = ((IPackageFragment) getArguments().getDestination()).getElementName();  

        return true;
    }

    /**
     * Name of this class. 
     * <p>
     * {@inheritDoc}
     */
    @Override
    public final String getName() {
        return "JML Field Move Participant";
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
     * Computes the changes which need to be done to the JML code and
     * add those to the changes to the java code which are already scheduled.
     * 
     * @return Returns null if only shared text changes are made. Otherwise
     *      returns a {@link TextChange} which gathered all the changes to JML annotations 
     *      in classes which do not have any Java changes scheduled.
     *
     */
    public final Change createChange(final IProgressMonitor pm) throws CoreException,
    OperationCanceledException {

        // Only non empty change objects will be added
        ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();
        
        ClassMoveRefactoringComputer changesComputer = new ClassMoveRefactoringComputer(fOldPackName, fNewPackName, fOldFullQualName);

        // Find out the projects which need to be checked: active project plus all dependencies
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
        projectsToCheck.add(fProject);

        try {// Look through all source files in each package and project
            for (final IJavaProject project :  RefactoringUtil.getAllProjectsToCheck(projectsToCheck, fProject)) {
                for (final IPackageFragment pac : RefactoringUtil.getAllPackageFragmentsContainingSources(project)) {
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {

                        final ArrayList<ReplaceEdit> changesToJML = changesComputer.computeNeededChangesToJML(
                                unit, project);

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
                            // In case changes to the JML code needs to be done (but not to the java code)
                            if (!changesToJML.isEmpty()){

                                changesToFilesWithoutJavaChanges.add(RefactoringUtil.combineEditsToChange(
                                        unit, changesToJML));
                            }
                        }
                    }
                }
            }
        }
        catch (final JavaModelException e) {
            return null;
        }

        // After iterating through all needed projects and source files, determine what needs to be returned.    
        return RefactoringUtil.assembleChangeObject(changesToFilesWithoutJavaChanges);
    }
}
