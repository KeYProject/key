package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;

import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;

public class RefactoringUtilities {

    /**
     * 
     * @param project
     * @return
     * @throws JavaModelException
     */
    public static ArrayList<IPackageFragment> getAllPackageFragmentsContainingSources(final IJavaProject project) throws JavaModelException {
        
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
