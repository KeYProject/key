package org.key_project.jmlediting.profile.jmlref.refactoring;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.PackageFragment;
import org.eclipse.jdt.internal.core.SourceMethod;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.MoveParticipant;

public class MoveParticipantSMethod extends MoveParticipant {

    private SourceMethod methodToMove;        // file
    private String methName;
    
    private String oldClassName;                // file name
    private String newClassName;
    
    private String fOldPackName;            // old package name
    private String fNewPackName;            // new package name
    
    @SuppressWarnings("restriction")
    @Override
    protected boolean initialize(Object element) {
        if(element instanceof SourceMethod){
            methodToMove=(SourceMethod) element;
            methName=methodToMove.getElementName();
            System.out.println(methName);
            //System.out.println(((SourceMethod) element).getParent().getElementName());
            // get the old and new package name , because we only want to replace package names, otherwise nested classes problem        
            // fOldPackName = fOldFullQualName.substring(0, fOldFullQualName.indexOf(fDocName)-1);
            // fNewPackName = ((PackageFragment) getArguments().getDestination()).getElementName();  

            return true;
        }else{
            return false;
        }
    }

    @Override
    public String getName() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public RefactoringStatus checkConditions(IProgressMonitor pm,
            CheckConditionsContext context) throws OperationCanceledException {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public Change createChange(IProgressMonitor pm) throws CoreException,
            OperationCanceledException {
        // TODO Auto-generated method stub
        return null;
    }

}
