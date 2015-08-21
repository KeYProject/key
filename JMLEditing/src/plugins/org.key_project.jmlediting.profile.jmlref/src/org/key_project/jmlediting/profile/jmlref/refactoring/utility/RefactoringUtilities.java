package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.util.jdt.JDTUtil;

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
    
    /**
     * 
     * @param projectsToCheck
     * @param refactoringStartingProject
     * @throws JavaModelException
     */
    public static void getAllProjectsToCheck(ArrayList<IJavaProject> projectsToCheck, IJavaProject refactoringStartingProject)
            throws JavaModelException {
        // Iterate through all java projects and check for projects which require the active project
        IJavaProject[] allProjects = JDTUtil.getAllJavaProjects();
        
        for (IJavaProject project: allProjects){
            String[] requiredProjectNames = project.getRequiredProjectNames();
            
            if (requiredProjectNames.length > 0) {
                
                for (String requiredProject: requiredProjectNames){
                    
                    if (requiredProject.equals(refactoringStartingProject.getElementName())) {
                        projectsToCheck.add(project);
                    }
                } 
            }
        }
    }

    /**
     * 
     * @param packToRename
     * @return
     * @throws JavaModelException
     */
    public static ArrayList<String> getAllQualifiedNamesOfClasses(IPackageFragment packToRename) throws JavaModelException {
        ArrayList<String> allQualifiedNames = new ArrayList<String>();
        
        String packageName = packToRename.getElementName();
        
        ICompilationUnit[] compilationUnits = packToRename.getCompilationUnits();
        
        // Combine the package name with the class names.
        for (ICompilationUnit unit : compilationUnits){
            
            String className = unit.getElementName();
            
            allQualifiedNames.add(packageName + "." + className.substring(0, className.lastIndexOf('.')));
        }
        
        return allQualifiedNames;
    }
}
