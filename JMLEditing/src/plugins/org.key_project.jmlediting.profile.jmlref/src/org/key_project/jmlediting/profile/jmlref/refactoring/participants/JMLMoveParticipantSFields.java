package org.key_project.jmlediting.profile.jmlref.refactoring.participants;

import java.util.ArrayList;
import java.util.Arrays;

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
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.FieldMoveRefactoringComputer;
import org.key_project.util.jdt.JDTUtil;

/**
 * Class to participate in the move refactoring of static fields.
 * 
 * It uses the {@link CommentLocator} to get a list of all JML comments.
 * The changes are added to the scheduled java changes as the JDT takes care of 
 * moving offsets in the editor and preview when several changes are made to the same file.
 * 
 * @author Maksim Melnik
 */
public class JMLMoveParticipantSFields extends MoveParticipant {

    private IJavaElement fieldToMove;        // field
    private String fieldName;
    
    private String oldClassFullQualName;                // fully qualified name of the old class
    private String newClassFullQualName;
    
    /**
     * {@inheritDoc} Initializes the source and destination paths, aswell as the field to move itself.
     */
    @Override
    protected boolean initialize(Object element) {
        if(element instanceof IJavaElement){
            fieldToMove=(IJavaElement) element;
            fieldName=fieldToMove.getElementName();
            oldClassFullQualName=((IType) fieldToMove.getParent()).getFullyQualifiedName();
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
    public String getName() {
        return "JML Field Move Participant";
    }

    /**
     * Do nothing.
     *
     * {@inheritDoc}
     */
    @Override
    public RefactoringStatus checkConditions(IProgressMonitor pm,
            CheckConditionsContext context) throws OperationCanceledException {
        return new RefactoringStatus();
    }

    @Override
    public Change createChange(IProgressMonitor pm) throws CoreException,
            OperationCanceledException {

        // Only non empty change objects will be added
        ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();

        // Find out the projects which need to be checked: active project plus all dependencies
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>(Arrays.asList(JDTUtil.getAllJavaProjects()));
        
        //TODO: IF METHOD IS NOT STATIC RETURN EMPTY LIST
        
        try {
            // Look through all source files in each package and project
            for (final IJavaProject project : projectsToCheck) {
                for (final IPackageFragment pac : project.getPackageFragments()) {
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {

                        FieldMoveRefactoringComputer changesComputer = new FieldMoveRefactoringComputer(oldClassFullQualName, newClassFullQualName, fieldName);
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
        else {
            CompositeChange allChangesToFilesWithoutJavaChanges = new CompositeChange("Changes to JML");
            for (TextFileChange change : changesToFilesWithoutJavaChanges){
                allChangesToFilesWithoutJavaChanges.add(change);
            }
            return allChangesToFilesWithoutJavaChanges;
        }
    }
}
