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
            for (final IJavaProject project : RefactoringUtil.getAllProjectsToCheck(projectsToCheck, fProject)) {
                for (final IPackageFragment pac : RefactoringUtil.getAllPackageFragmentsContainingSources(project)) {
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {

                        //TODO: absolutely horrible. Better try to do all changes to java code and run JML then.
                        // TODO: but refactoring computer / resolving of Class.field needs to be rewritten.
                        // Get scheduled changes to the java code from the rename processor
                        final TextChange changesToJavaCode = getTextChange(unit);
                        
                        FieldAndMethodMoveRefactoringComputer changesComputer = new FieldAndMethodMoveRefactoringComputer(oldClassFullQualName, newClassFullQualName, elementName, unit);
                        
                        ArrayList<ReplaceEdit> changesToJML = changesComputer.computeNeededChangesToJML(unit, project);

                        if (!changesToJML.isEmpty() && changesToJavaCode != null) { 
                            // add our edits to the java changes
                            // JDT will compute the shifts and the preview
                                
                            // Choose the right place in the tree to add the JML edits.
                            // changesToJavaCode is a MultiTextEdit (as a root) consisting of a MultiTextEdit consisting of Edits 
                            MultiTextEdit presetRootEdit = (MultiTextEdit) changesToJavaCode.getEdit();                              
                            MultiTextEdit givenMultiEdit = (MultiTextEdit) presetRootEdit.getChildren()[0];
                            
                            if (RefactoringUtil.hasNoOverlapping(changesToJML, presetRootEdit)){
                                for(ReplaceEdit editToJML : changesToJML){
                                    presetRootEdit.addChild(editToJML);
                                }
                                changesToJavaCode.perform(pm);
                                changesToJavaCode.dispose();
                                
                                changesComputer = new FieldAndMethodMoveRefactoringComputer(oldClassFullQualName, newClassFullQualName, elementName, unit);
                                changesToJML = changesComputer.computeNeededChangesToJML(unit, project);
                                
                                if (!changesToJML.isEmpty()){
                                    changesToFilesWithoutJavaChanges.add(RefactoringUtil.combineEditsToChange(
                                            unit, changesToJML));
                                }
                            }
                            else if (RefactoringUtil.hasNoOverlapping(changesToJML, givenMultiEdit)){
                                for(ReplaceEdit editToJML : changesToJML){
                                    givenMultiEdit.addChild(editToJML);
                                }
                                changesToJavaCode.perform(pm);
                                changesToJavaCode.dispose();
                                
                                changesComputer = new FieldAndMethodMoveRefactoringComputer(oldClassFullQualName, newClassFullQualName, elementName, unit);
                                changesToJML = changesComputer.computeNeededChangesToJML(unit, project);
                                
                                if (!changesToJML.isEmpty()){
                                    changesToFilesWithoutJavaChanges.add(RefactoringUtil.combineEditsToChange(
                                            unit, changesToJML));
                                }
                            }
                            else { // perform the changes to the java code and recompute the JML changes
                                changesToJavaCode.perform(pm);
                                changesToJavaCode.dispose();
                                
                                changesComputer = new FieldAndMethodMoveRefactoringComputer(oldClassFullQualName, newClassFullQualName, elementName, unit);
                                changesToJML = changesComputer.computeNeededChangesToJML(unit, project);
                                
                                if (!changesToJML.isEmpty()){
                                    changesToFilesWithoutJavaChanges.add(RefactoringUtil.combineEditsToChange(
                                            unit, changesToJML));
                                }
                            }
                        }
                        else if (!changesToJML.isEmpty() && changesToJavaCode == null) {
                            // In case changes to the JML code needs to be done (but not to the java code)
                            changesToFilesWithoutJavaChanges.add(RefactoringUtil.combineEditsToChange(
                                    unit, changesToJML));
                        }
                        else if (changesToJavaCode != null && changesToJML.isEmpty()) {
                            changesToJavaCode.perform(pm);
                            changesToJavaCode.dispose();
                            
                            changesComputer = new FieldAndMethodMoveRefactoringComputer(oldClassFullQualName, newClassFullQualName, elementName, unit);
                            changesToJML = changesComputer.computeNeededChangesToJML(unit, project);
                            
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
