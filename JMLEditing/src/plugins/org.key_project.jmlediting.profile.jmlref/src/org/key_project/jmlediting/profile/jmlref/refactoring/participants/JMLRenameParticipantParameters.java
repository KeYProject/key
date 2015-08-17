package org.key_project.jmlediting.profile.jmlref.refactoring.participants;

import java.util.ArrayList;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.ILocalVariable;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.profile.jmlref.refactoring.utility.DefaultRenameRefactoringComputer;

/**
 * Renaming of method parameters
 * 
 * @author Robert Heimbach
 *
 */
public class JMLRenameParticipantParameters extends RenameParticipant {

    private String fNewName;
    private String fOldName;
    private ICompilationUnit fCompUnit;
    private ILocalVariable fLocalVar;
    private IJavaProject fProject;
    
    @Override
    protected boolean initialize(Object element) {
        fNewName = getArguments().getNewName();
        fLocalVar = (ILocalVariable) element;
        
        // check if it is a method parameter
        // has a declaring method and a compilation unit
        if (fLocalVar.isParameter() && fLocalVar.getDeclaringMember().getElementType() == IJavaElement.METHOD
                && !(fLocalVar.getDeclaringMember().getCompilationUnit() == null)) {
            fOldName = fLocalVar.getElementName();
            fProject = fLocalVar.getJavaProject();
            fCompUnit = fLocalVar.getDeclaringMember().getCompilationUnit();

            return true;
            }
        else {
            return false;
        }
    }

    @Override
    public String getName() {
        return "JML Local Variables Refactoring Rename Participant";
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

        DefaultRenameRefactoringComputer changesComputer = new DefaultRenameRefactoringComputer(fOldName, fLocalVar, fNewName);

        final ArrayList<ReplaceEdit> changesToJML = changesComputer.computeNeededChangesToJML(
                fCompUnit, fProject);
        
        // Get scheduled changes to the java code from the rename processor
        final TextChange changesToJavaCode = getTextChange(fCompUnit);

        // add our edits to the java changes
        // JDT will compute the shifts and the preview
        if (changesToJavaCode != null) {
            for (final ReplaceEdit edit : changesToJML) {
                changesToJavaCode.addEdit(edit);
            }
        }
        
        return null;
    }
}
