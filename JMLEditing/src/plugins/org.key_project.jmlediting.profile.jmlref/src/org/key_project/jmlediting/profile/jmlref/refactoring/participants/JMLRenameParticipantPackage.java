package org.key_project.jmlediting.profile.jmlref.refactoring.participants;

import java.util.ArrayList;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.corext.refactoring.rename.RenamePackageProcessor;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;

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
@SuppressWarnings("restriction")
public class JMLRenameParticipantPackage extends RenameParticipant {

    private IPackageFragment fPackageToRename;
    private String fNewName;
    private IJavaElement fJavaElementToRename;
    private String fOldName;

    /**
     * Name of this class. {@inheritDoc}
     */
    @Override
    public final String getName() {
        return "JML Package Refactoring Rename Participant";
    }
    
    @Override
    protected boolean initialize(Object element) { 
        fJavaElementToRename = (IJavaElement) element;
        fOldName = fJavaElementToRename.getElementName();
        fPackageToRename = (IPackageFragment) element;
        boolean fRenameSubpackages = ((RenamePackageProcessor) getProcessor()).getRenameSubpackages();
        ArrayList<String> allQualNamesToCheckFor = getAllClassnamesInPackage(fPackageToRename, fRenameSubpackages);
        
        // Only something to change in JML if the package contains Java resources.
        try {
            return (fPackageToRename.containsJavaResources());
        }
        catch (JavaModelException e) {
           return false;
        }
    }

    private ArrayList<String> getAllClassnamesInPackage(
            IPackageFragment packToRename, boolean renameSubpackages) {
        
        return null;
    }

    @Override
    public RefactoringStatus checkConditions(IProgressMonitor pm,
            CheckConditionsContext context) throws OperationCanceledException {
        return new RefactoringStatus();
    }

    @Override
    public Change createChange(IProgressMonitor pm) throws CoreException,
            OperationCanceledException {
        return null;
    }

}
