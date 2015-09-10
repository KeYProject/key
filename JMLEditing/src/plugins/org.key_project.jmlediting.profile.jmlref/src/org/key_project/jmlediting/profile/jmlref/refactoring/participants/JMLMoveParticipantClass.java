package org.key_project.jmlediting.profile.jmlref.refactoring.participants;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.PackageFragment;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.MoveParticipant;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.ClassMoveRefactoringComputer;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RefactoringUtilities;

/**
 * Class to participate in the move refactoring of java classes.
 * 
 * It uses the {@link CommentLocator} to get a list of all JML comments.
 * The changes are added to the scheduled java changes as the JDT takes care of 
 * moving offsets in the editor and preview when several changes are made to the same file.
 * 
 * @author Maksim Melnik
 */
@SuppressWarnings("restriction")
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
        if(element instanceof IJavaElement){
            fToMove=(IJavaElement) element;

            fDocName = fToMove.getElementName();
            fOldFullQualName=((IType) element).getFullyQualifiedName();

            fProject = fToMove.getJavaProject();
            
            // get the old and new package name , because we only want to replace package names, otherwise nested classes problem        
            fOldPackName = fOldFullQualName.substring(0, fOldFullQualName.indexOf(fDocName)-1);
            fNewPackName = ((PackageFragment) getArguments().getDestination()).getElementName();  

            return true;
        }else{
            return false;
        }
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
     *      returns a TextChange Object which gathered all the changes to JML annotations 
     *      in class which does not have any Java changes scheduled.
     *
     */
    public final Change createChange(final IProgressMonitor pm) throws CoreException,
    OperationCanceledException {

        // Only non empty change objects will be added
        ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();

        // Find out the projects which need to be checked: active project plus all dependencies
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
        projectsToCheck.add(fProject);

        try {
            RefactoringUtilities.getAllProjectsToCheck(projectsToCheck, fProject);
            
            // Look through all source files in each package and project
            for (final IJavaProject project : projectsToCheck) {
                for (final IPackageFragment pac : RefactoringUtilities.getAllPackageFragmentsContainingSources(project)) {
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {

                        ClassMoveRefactoringComputer changesComputer = new ClassMoveRefactoringComputer(fOldPackName, fNewPackName, fOldFullQualName);
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

                                // Gather all the edits to the text (JML annotations) in a MultiTextEdit
                                // and add those to a change object for the given file
                                TextFileChange tfChange = new TextFileChange("", (IFile) unit.getCorrespondingResource());                         
                                MultiTextEdit allEdits = new MultiTextEdit();

                                for (final ReplaceEdit edit: changesToJML) {
                                    allEdits.addChild(edit);
                                }

                                tfChange.setEdit(allEdits);

                                changesToFilesWithoutJavaChanges.add(tfChange);
                            }
                        }
                    }
                }
            }
        }
        catch (final JavaModelException e) {
            return null;
        }

        // Return null if only shared changes, otherwise gather changes to JML for classes with no java changes.
        if (changesToFilesWithoutJavaChanges.isEmpty())
            return null;
        else if (changesToFilesWithoutJavaChanges.size() == 1){
            return changesToFilesWithoutJavaChanges.get(0);
        }
        else {
         // Create a composite change to gather all the changes (effect in preview: a tree item one level higher without preview is added)
            CompositeChange allChangesToFilesWithoutJavaChanges = new CompositeChange("Changes to JML");
            for (TextFileChange change : changesToFilesWithoutJavaChanges){
                allChangesToFilesWithoutJavaChanges.add(change);
            }
            return allChangesToFilesWithoutJavaChanges;
        }
    }
}
