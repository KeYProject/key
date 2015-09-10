package org.key_project.jmlediting.profile.jmlref.refactoring.participants;

import java.util.ArrayList;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.SourceMethod;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.MoveParticipant;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.MethodMoveRefactoringComputer;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RefactoringUtilities;

/**
 * 
 * @author Maksim Melnik
 *
 */
@SuppressWarnings("restriction") // SourceMethod accessed.
public class JMLMoveParticipantSMethod extends MoveParticipant {

    private SourceMethod methodToMove;
    private String methName;
    
    private String oldClassFullQualName;        // fully qualified names of old and new classes
    private String newClassFullQualName;
    private IJavaProject fProject;
    
    /**
     * {@inheritDoc} Initializes the source and destination paths, aswell as the method to move itself.
     */
    @Override
    protected final boolean initialize(Object element) {
        if(element instanceof SourceMethod){
            methodToMove=(SourceMethod) element;
            methName=methodToMove.getElementName();
            fProject = methodToMove.getJavaProject();
            oldClassFullQualName=((IType) methodToMove.getParent()).getFullyQualifiedName();
            newClassFullQualName=((IType) getArguments().getDestination()).getFullyQualifiedName();
            return true;
        }else{
            return false;
        }
    }

    /**
     * Name of this class. {@inheritDoc}
     */
    @Override
    public final String getName() {
        return "JML Method Move Participant";
    }

    /**
     * Do nothing.
     *
     * {@inheritDoc}
     */
    @Override
    public final RefactoringStatus checkConditions(IProgressMonitor pm,
            CheckConditionsContext context) throws OperationCanceledException {
        return new RefactoringStatus();
    }

    @Override
    public final Change createChange(IProgressMonitor pm) throws CoreException,
            OperationCanceledException {

        // Only non empty change objects will be added
        ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();

        // Find out the projects which need to be checked: active project plus all dependencies
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
        projectsToCheck.add(fProject);
        
        try {
            // Look through all source files in each package and project
            for (final IJavaProject project : projectsToCheck) {
                for (final IPackageFragment pac : RefactoringUtilities.getAllPackageFragmentsContainingSources(project)) {
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {

                        MethodMoveRefactoringComputer changesComputer = new MethodMoveRefactoringComputer(oldClassFullQualName, newClassFullQualName, methName);
                        final ArrayList<ReplaceEdit> changesToJML = changesComputer.computeNeededChangesToJML(unit, project);

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
