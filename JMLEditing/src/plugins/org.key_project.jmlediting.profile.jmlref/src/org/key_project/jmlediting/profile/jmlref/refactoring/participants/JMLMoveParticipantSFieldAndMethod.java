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
 * @author Maksim Melnik, Robert Heimbach
 */
public class JMLMoveParticipantSFieldAndMethod extends MoveParticipant {

    private IJavaElement elementToMove;        
    private String elementName;
    
    private String oldClassFullQualName;                // fully qualified name of the old class
    private String newClassFullQualName;
    private IJavaProject fProject;
    
    /**
     * {@inheritDoc} Saves the element which is moved, the name of the element,
     * its source and destination class, as well as the project starting the refactoring.
     */
    @Override
    protected final boolean initialize(Object element) {
        elementToMove = (IJavaElement) element;           
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
     * Computes the changes which need to be done to the JML code and
     * add those to the changes to the java code which are already scheduled.
     * Note that the moving of methods and fields creates {@link TextEdit}s 
     * which are covering a large Region and thus the adding to the given java 
     * code changes needs to be done carefully.
     * 
     * @return Returns null if only shared text changes are made. Otherwise
     *      returns a {@link TextChange} which gathered all the changes to JML annotations 
     *      in classes which do not have any Java changes scheduled.
     *
     */
    //@Override
    public final Change createChange(IProgressMonitor pm) throws CoreException,
            OperationCanceledException {

        // Only non empty change objects will be added
        ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();
        
        // Find out the projects which need to be checked: active project plus all dependencies
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
        projectsToCheck.add(fProject);
        
        try {
            // Look through all source files in each package and project
            for (final IJavaProject project : RefactoringUtil.getAllProjectsToCheck(projectsToCheck, fProject)) {
                for (final IPackageFragment pac : RefactoringUtil.getAllPackageFragmentsContainingSources(project)) {
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {

                        FieldAndMethodMoveRefactoringComputer changesComputer = new FieldAndMethodMoveRefactoringComputer(oldClassFullQualName, newClassFullQualName, elementName, unit);
                        
                        final ArrayList<ReplaceEdit> changesToJML = changesComputer.computeNeededChangesToJML(unit, project);

                        if (!changesToJML.isEmpty()) {
                            
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
                                
                                TextEdit givenMultiEdit = presetRootEdit.getChildren()[0];
                                
                                // Check if we can add it next to the given multi edit to the root
                                if (!RefactoringUtil.isOverlapping(presetRootEdit, regionJML)) {
                                    presetRootEdit.addChild(jmlEditsCombined);
                                }
                                // else check if we can add it into the given multi edit as a child
                                else if (!RefactoringUtil.isOverlapping(givenMultiEdit, regionJML)){
                                    givenMultiEdit.addChild(jmlEditsCombined);
                                }
                                // we could not add them all together (better preview tree) -> so try to add them individually
                                else {
                                    for (ReplaceEdit edit : changesToJML){
                                        if (!RefactoringUtil.isOverlapping(givenMultiEdit, edit.getRegion())){
                                            // create a copy of the edit we want to put in because we need one without an already set parent
                                            ReplaceEdit newEdit = new ReplaceEdit(edit.getOffset(), edit.getLength(), edit.getText());
                                            givenMultiEdit.addChild(newEdit);
                                        }
                                    }
                                }
                            }
                            else {
                                // In case changes to the JML code needs to be done (but not to the java code)
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
