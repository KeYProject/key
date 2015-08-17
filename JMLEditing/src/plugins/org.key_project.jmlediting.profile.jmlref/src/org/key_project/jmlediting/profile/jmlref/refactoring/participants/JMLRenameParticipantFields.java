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
import org.eclipse.jdt.core.IPackageFragmentRoot;
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
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.DefaultRenameRefactoringComputer;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.util.jdt.JDTUtil;

/**
 * Class to participate in the rename refactoring of java fields.
 * 
 * It uses the {@link CommentLocator} to get a list of all JML comments and 
 * the {@link Resolver} to determine if the field to be renamed is referenced.
 * The changes are added to the scheduled java changes as the JDT takes care of 
 * moving offsets in the editor and preview when several changes are made to the same file.
 * 
 * The class usually returns NULL because changes are added in-place to the Java changes except
 * if changes to JML annotations to a class need to be made for which no Java changes are needed.
 * 
 * To reduce the number of times the resolver is used, the JML annotations are first taken
 * in the form of StringNodes as filtered before the primary Nodes are computed which are 
 * then taken to the Resolver. 
 * 
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
     * {@inheritDoc} Saves the new name to change to. Saves the old name and the
     * field to be changed as a IJavaElement to search for references to it. Saves
     * the active Project, i.e. the project which contains the class which field changes.
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
     *
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
     * returns a TextChange Object which gathered all the changes to JML annotations 
     * in class which does not have any Java changes scheduled.
     * 
     *  {@inheritDoc}
     *
     */
    @Override
    public Change createChange(final IProgressMonitor pm) throws CoreException,
            OperationCanceledException {

        // Only non empty change objects will be added
        ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();
        
        // Find out the projects which need to be checked: active project plus all dependencies
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
        projectsToCheck.add(fProject);

        try {
            // Iterate through all java projects and check for projects which require the active project
            IJavaProject[] allProjects = JDTUtil.getAllJavaProjects();
            
            for (IJavaProject project: allProjects){
                String[] requiredProjectNames = project.getRequiredProjectNames();
                
                if (requiredProjectNames.length > 0) {
                    
                    for (String requiredProject: requiredProjectNames){
                        
                        if (requiredProject.equals(fProject.getElementName())) {
                            projectsToCheck.add(project);
                        }
                    } 
                }
            }
            
            // Look through all source files in each package and project
            for (final IJavaProject project : projectsToCheck) {
                for (final IPackageFragment pac : getAllPackageFragmentsContainingSources(project)) {
                    for (final ICompilationUnit unit : pac.getCompilationUnits()) {
                        
                        DefaultRenameRefactoringComputer changesComputer = new DefaultRenameRefactoringComputer(fOldName, fJavaElementToRename, fNewName);
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
        else {
            CompositeChange allChangesToFilesWithoutJavaChanges = new CompositeChange("Changes to JML");
            for (TextFileChange change : changesToFilesWithoutJavaChanges){
                allChangesToFilesWithoutJavaChanges.add(change);
            }
            return allChangesToFilesWithoutJavaChanges;
        }
    }

    
    private ArrayList<IPackageFragment> getAllPackageFragmentsContainingSources(IJavaProject project) throws JavaModelException {
        
        ArrayList<IPackageFragment> allFragments = new ArrayList<IPackageFragment>();
        
        IPackageFragmentRoot[] roots = project.getPackageFragmentRoots();
        
        // Checks each roots if it contains source/class files and adds those to the arraylist.
        for (IPackageFragmentRoot root: roots){
            if (!root.isArchive()) {
                IJavaElement[] children = root.getChildren();            
                for (IJavaElement child: children){
                    if (child.getElementType() == IJavaElement.PACKAGE_FRAGMENT)
                        allFragments.add((IPackageFragment)child);
                }
            }
        }
        
        return allFragments;
    }

    
}