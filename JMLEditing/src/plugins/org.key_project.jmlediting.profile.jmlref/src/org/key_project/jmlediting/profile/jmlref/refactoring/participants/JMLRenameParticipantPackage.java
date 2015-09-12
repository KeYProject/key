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
 * Class to participate in the refactoring renaming of packages.
 * <p>
 * Conceptually, renaming a package is equivalent to moving all classes in the renamed 
 * package to the newly created package. Thus, this participant uses the {@link ClassMoveRefactoringComputer}
 * to search through all classes in each (necessary) project for references to classes which were located
 * in the renamed package and using the fully qualified name, i.e. naming the path with all 
 * the packages. </p>
 * <p>
 * Note that JDT takes care of the "Rename subpackages" option by calling this participant
 * on each subpackage which needs to be renamed. </p>
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
     * Name of this class. <p>{@inheritDoc}
     */
    @Override
    public final String getName() {
        return "JML Package Refactoring Rename Participant";
    }
    
    
    /**
     * {@inheritDoc} <p>
     * Extract and save all the information we need to carry out the package renaming.
     * In particular, a list of the fully qualified names of all classes which are located
     * in the package to be renamed is created because occurrences of those Strings need
     * to be replaced in the JML annotations.
     */
    @Override
    protected final boolean initialize(Object element) { 
        fJavaElementToRename = (IJavaElement) element;
        fOldName = fJavaElementToRename.getElementName();
        fProject = fJavaElementToRename.getJavaProject();
        fNewName = getArguments().getNewName();
        fPackageToRename = (IPackageFragment) element;
        
        // Search through the package for java classes and save all the qualified class names.
        // Occurrences in JML like this need to be changed.
        try {
            fAllQualifiedNamesToSearchFor = RefactoringUtilities.getAllQualifiedNamesOfClasses(fPackageToRename);
            
            return (fAllQualifiedNamesToSearchFor.size() > 0);
        } 
        // If there were any problems accessing the folder structure and the classes therein.
        catch (JavaModelException e) {
           return false;
        }
    }

    /**
     * <p>
     * No checking. Changes are directly done.
     * </p>
     * {@inheritDoc}
     */
    @Override
    public final RefactoringStatus checkConditions(IProgressMonitor pm,
            CheckConditionsContext context) throws OperationCanceledException {
        return new RefactoringStatus();
    }

    
    /**
     * <p>
     * Creating the changes which need to be done to the JML annotations. </p>
     * <p>
     * The process is the following: Determining which projects need to be checked, 
     * iterating through all the packages and classes in those projects and search for
     * any fully qualified references to classes which are located in the renamed package.
     * </p> 
     * {@inheritDoc}
     */
    @Override
    public final Change createChange(IProgressMonitor pm) throws CoreException,
            OperationCanceledException {

        // To accumulate all changes to files without java (text) changes.
        // Only non empty change objects will be added to this
        ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();
        
        // Find out the projects which need to be checked: 
        // Active project plus all projects which depend on / require this.
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
        projectsToCheck.add(fProject);

        try {
            RefactoringUtilities.getAllProjectsToCheck(projectsToCheck, fProject);
            
            // Look through all source files in each package and project
            for (final IJavaProject project : projectsToCheck) {
                for (final IPackageFragment pac : RefactoringUtilities.getAllPackageFragmentsContainingSources(project)) {
                    for (final ICompilationUnit unit : pac.getCompilationUnits()) {
                        
                        // Several classes could potentially be referenced but RefcatoringComputer can only search for one at a time.
                        // Thus iterate through all the potential references.
                        ArrayList<ReplaceEdit> allChangesToJMLinUnit = new ArrayList<ReplaceEdit>();
                        
                        for (String potentialReference : fAllQualifiedNamesToSearchFor) {
                        
                            ClassMoveRefactoringComputer changesComputer = new ClassMoveRefactoringComputer(fOldName, fNewName, potentialReference);
                            final ArrayList<ReplaceEdit> changesToJML = changesComputer.computeNeededChangesToJML(
                                unit, project);
                            
                            if (changesToJML.size() > 0) {
                                allChangesToJMLinUnit.addAll(changesToJML);
                            }
                        }

                        // Get scheduled changes to the java code from the rename processor
                        final TextChange changesToJavaCode = getTextChange(unit);

                        // add our edits to the java changes
                        // JDT will compute the shifts and the preview
                        if (changesToJavaCode != null) {
                            for (final ReplaceEdit edit : allChangesToJMLinUnit) {
                                changesToJavaCode.addEdit(edit);
                            }
                        }
                        else {
                            // In case changes to the JML code needs to be done (but not to the java code)
                            if (!allChangesToJMLinUnit.isEmpty()){
                                
                                // Gather all the edits to the text (JML annotations) in a MultiTextEdit
                                // and add those to a change object for the given file
                                TextFileChange tfChange = new TextFileChange("", (IFile) unit.getCorrespondingResource());                         
                                MultiTextEdit allEdits = new MultiTextEdit();
                                
                                for (final ReplaceEdit edit: allChangesToJMLinUnit) {
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