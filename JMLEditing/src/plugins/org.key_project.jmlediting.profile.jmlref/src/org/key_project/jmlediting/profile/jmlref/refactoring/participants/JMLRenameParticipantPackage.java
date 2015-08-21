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
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.ClassMoveRefactoringComputer;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.RefactoringUtilities;

/**
 * Conceptually this is a move of all classes in the renamed package to the 
 * newly created package.
 * 
 * Get all classes in the package and, in case "rename subpackages" was activated, also subpackages.
 * Search through all classes in the project if the use package.subpackage.Classname in JML.
 * 
 * @author Robert Heimbach
 *
 */
public class JMLRenameParticipantPackage extends RenameParticipant {

    private IPackageFragment fPackageToRename;
    private String fNewName;
    private IJavaElement fJavaElementToRename;
    private String fOldName;
    private ArrayList<String> fAllQualifiedNamesToSearchFor;
    private IJavaProject fProject;

    /**
     * Name of this class. {@inheritDoc}
     */
    @Override
    public final String getName() {
        return "JML Package Refactoring Rename Participant";
    }
    
    @Override
    protected boolean initialize(Object element) { 
        System.out.println("activated");
        
        fJavaElementToRename = (IJavaElement) element;
        fOldName = fJavaElementToRename.getElementName();
        fProject = fJavaElementToRename.getJavaProject();
        fNewName = getArguments().getNewName();
        fPackageToRename = (IPackageFragment) element;
        
        try {
            fAllQualifiedNamesToSearchFor = RefactoringUtilities.getAllQualifiedNamesOfClasses(fPackageToRename);
            System.out.println(fAllQualifiedNamesToSearchFor);
            
            // Only something to change to JML if the package contains Java resources.
            return (fAllQualifiedNamesToSearchFor.size() > 0);
        } // If there were any problems accessing the folder structure and the classes therein.
        catch (JavaModelException e) {
           return false;
        }
    }

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
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
        projectsToCheck.add(fProject);

        try {
            RefactoringUtilities.getAllProjectsToCheck(projectsToCheck, fProject);
            
            // Look through all source files in each package and project
            for (final IJavaProject project : projectsToCheck) {
                for (final IPackageFragment pac : RefactoringUtilities.getAllPackageFragmentsContainingSources(project)) {
                    for (final ICompilationUnit unit : pac.getCompilationUnits()) {
                        
                        ClassMoveRefactoringComputer changesComputer = new ClassMoveRefactoringComputer(fOldName, fNewName, fAllQualifiedNamesToSearchFor.get(0));
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
        // Create a composite change to gather all the changes (effect in preview: a tree item above without preview)
        else {
            CompositeChange allChangesToFilesWithoutJavaChanges = new CompositeChange("Changes to JML");
            for (TextFileChange change : changesToFilesWithoutJavaChanges){
                allChangesToFilesWithoutJavaChanges.add(change);
            }
            return allChangesToFilesWithoutJavaChanges;
        }
    }

}
