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
import org.eclipse.jface.text.IRegion;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.MoveParticipant;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.eclipse.text.edits.TextEdit;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.FieldAndMethodMoveRefactoringComputer;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RefactoringUtil;

/**
 * Class to participate in the move refactoring of static fields and methods.
 * 
 * @author Maksim Melnik
 */
public class JMLMoveParticipantSFieldAndMethod extends MoveParticipant {

    private IJavaElement elementToMove;        
    private String elementName;
    
    private String oldClassFullQualName;                // fully qualified name of the old class
    private String newClassFullQualName;
    private IJavaProject fProject;
    
    /**
     * {@inheritDoc} Initializes the source and destination paths, aswell as the field to move itself.
     */
    @Override
    protected final boolean initialize(Object element) {
        if(element instanceof IJavaElement){
            elementToMove = (IJavaElement) element;           
            fProject = elementToMove.getJavaProject();
            elementName = elementToMove.getElementName();
            oldClassFullQualName = ((IType) elementToMove.getParent()).getFullyQualifiedName();
            IType destination = (IType) getArguments().getDestination();
            newClassFullQualName = destination.getFullyQualifiedName();
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
     * Computes the changes which need to be done to the JML code and
     * add those to the changes to the java code which are already scheduled.
     * Note that the moving of methods and fields creates {@link TextEdit}s 
     * which are covering a large Region and thus the adding to the given java 
     * code changes needs to be done carefully.
     * 
     * @return Returns null if only shared text changes are made. Otherwise
     *      returns a TextChange Object which gathered all the changes to JML annotations 
     *      in class which does not have any Java changes scheduled.
     *
     */
    @Override
    public final Change createChange(IProgressMonitor pm) throws CoreException,
            OperationCanceledException {

        // Only non empty change objects will be added
        ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();
        
        FieldAndMethodMoveRefactoringComputer changesComputer = new FieldAndMethodMoveRefactoringComputer(oldClassFullQualName, newClassFullQualName, elementName);

        // Find out the projects which need to be checked: active project plus all dependencies
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
        projectsToCheck.add(fProject);
        
        try {
            // Look through all source files in each package and project
            for (final IJavaProject project : RefactoringUtil.getAllProjectsToCheck(projectsToCheck, fProject)) {
                for (final IPackageFragment pac : RefactoringUtil.getAllPackageFragmentsContainingSources(project)) {
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {

                        final ArrayList<ReplaceEdit> changesToJML = changesComputer.computeNeededChangesToJML(unit, project);

                        // Get scheduled changes to the java code from the rename processor
                        final TextChange changesToJavaCode = getTextChange(unit);

                        // add our edits to the java changes
                        // JDT will compute the shifts and the preview
                        if (changesToJavaCode != null) {
                            
                            MultiTextEdit jmlEditsCombined = RefactoringUtil.combineEditsToMultiEdit(changesToJML);
   
                            // Choose the right place in the tree to add the JML edits.
                            // changesToJavaCode is a MultiTextEdit (as a root) consisting of a MultiTextEdit consisting of Edits
                            IRegion regionJML = jmlEditsCombined.getRegion();
                            
                            TextEdit presetRootEdit = changesToJavaCode.getEdit();
                            
                            TextEdit[] children = presetRootEdit.getChildren();
                            
                            // check if some child completely covers the JML region. Add it then.
                            // Otherwise add it as a separate child
                            boolean overlap = false;
                            boolean jmlAdded = false;
                            for (TextEdit child : children) {
                                if (RefactoringUtil.isCovering(child.getRegion(), regionJML)) {
                                    child.addChild(jmlEditsCombined);
                                    jmlAdded = true;
                                    break;
                                }
                                if (RefactoringUtil.isOverlapping(child.getRegion(), regionJML)){
                                    overlap = true;
                                }
                            }
                            
                            if(!jmlAdded && !overlap){
                                presetRootEdit.addChild(jmlEditsCombined);
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
