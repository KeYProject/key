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
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RefactoringUtilities;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RenameRefactoringComputer;

/**
 * Class to participate in the rename refactoring of java fields.
 * <p>
 * It uses the {@link RenameRefactoringComputer} to compute the changes which need to be done.
 * The changes are then added to the scheduled java changes as the JDT takes care of 
 * moving offsets in the editor and preview when several changes are made to the same file. </p>
 * <p>
 * The class usually returns NULL because changes are added in-place to the Java changes except
 * if changes to JML annotations to a class need to be made for which no Java changes are needed. </p>
 * 
 * @author Robert Heimbach
 */
public class JMLRenameParticipantFields extends RenameParticipant {

    private IJavaElement fJavaElementToRename;
    private String fNewName;
    private String fOldName;
    private IJavaProject fProject;  // the project which has the fields to be renamed

    /**
     * Name of this class. {@inheritDoc}
     */
    @Override
    public final String getName() {
        return "JML Field Refactoring Rename Participant";
    }

    /**
     * {@inheritDoc} 
     * <p> Saves the new name to change to. Saves the old name and the
     * field to be changed as a IJavaElement to search for references to it. Saves
     * the active Project, i.e. the project which contains the class which field changes.</p>
     */
    @Override
    protected final boolean initialize(final Object element) {
        fNewName = getArguments().getNewName();

        if (element instanceof IJavaElement) {
            fJavaElementToRename = (IJavaElement) element;
            fProject = fJavaElementToRename.getJavaProject();
            fOldName = fJavaElementToRename.getElementName();
            return true;
        }
        else {
            return false;
        }
    }

    /**
     * Do nothing.
     * <p>
     * {@inheritDoc}
     */
    @Override
    public final RefactoringStatus checkConditions(final IProgressMonitor pm,
            final CheckConditionsContext context)
            throws OperationCanceledException {

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
    @Override
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
                    for (final ICompilationUnit unit : pac.getCompilationUnits()) {
                        
                        RenameRefactoringComputer changesComputer = new RenameRefactoringComputer(fJavaElementToRename, fOldName, fNewName);
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
        
        // After iterating through all needed projects and source files, determine what needs to be returned:
        
        // Return null if only shared changes, otherwise gather changes to JML for classes with no java changes.
        if (changesToFilesWithoutJavaChanges.isEmpty())
            return null;
        else if (changesToFilesWithoutJavaChanges.size() == 1){
            return changesToFilesWithoutJavaChanges.get(0);
        }
        // Create a composite change to gather all the changes (effect in preview: a tree item one level higher without preview is added)
        else {
            CompositeChange allChangesToFilesWithoutJavaChanges = new CompositeChange("Changes to JML");
            for (TextFileChange change : changesToFilesWithoutJavaChanges){
                allChangesToFilesWithoutJavaChanges.add(change);
            }
            return allChangesToFilesWithoutJavaChanges;
        }
    }
}