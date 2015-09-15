package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IImportDeclaration;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IPackageDeclaration;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * Class to compute the changes which needs to be done to the JML annotations 
 * if a static field or method is moved. In particular, it specifies how the list of nodes is 
 * filtered, i.e. how the JML expression to be replaced is found.
 * 
 * @author Maksim Melnik
 *
 */
public class FieldAndMethodMoveRefactoringComputer extends
        AbstractRefactoringComputer {

    private String elementName;
    private String oldClassFullQualName;
    private String newClassFullQualName;
    private ICompilationUnit compUnit;
    
    /**
     * Constructor. Saves the fully qualified name of the classes the field/method should be moved from and moved
     * to as well as the name of the field/method to be moved.
     *  
     * @param oldClassFullQualName fully qualified name of the class the field/method is in.
     * @param newClassFullQualName fully qualified name of the class the field/method should be moved to.
     * @param elementName name of the field/method to be moved.
     */
    public FieldAndMethodMoveRefactoringComputer(String oldClassFullQualName,
            String newClassFullQualName, String elementName, ICompilationUnit unit) {
        this.oldClassFullQualName = oldClassFullQualName;
        this.newClassFullQualName = newClassFullQualName;
        this.elementName = elementName;
        this.compUnit = unit;
    }

    /**
     * Filters a list of {@link IASTNode} to exclude JML expression which does not need to be changed.
     * 
     * @param nodesList a list to be filtered. {@link IStringNode}s are expected.
     * @return list of filtered {@link IStringNode}s.
     */
    protected final List<IStringNode> filterStringNodes(List<IASTNode> nodesList) {
        final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
        String nodeString="";

        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;
            
            // combine the string nodes
            if((oldClassFullQualName+"."+elementName).contains(stringNode.getString()))
                nodeString=nodeString+stringNode.getString();
            // reset
            else nodeString="";
            
            if (nodeString.equals(oldClassFullQualName+"."+elementName)) {
                filteredList.add(stringNode);
            }
        }
        
        // check for not fully qualified access but access via import statement
        if (checkForNonFullyQualified()) {
            String oldClassName = oldClassFullQualName.substring(oldClassFullQualName.lastIndexOf('.')+1);
            
            nodeString = "";
            for (final IASTNode node: nodesList) {
                final IStringNode stringNode = (IStringNode) node;
             
                // combine the string nodes
                if((oldClassName+"."+elementName).contains(stringNode.getString()))
                    nodeString=nodeString+stringNode.getString();
                // reset
                else nodeString="";
                
                if (nodeString.equals(oldClassName+"."+elementName)) {
                    int start = stringNode.getStartOffset();
                    
                    boolean isContained = false;
                    for (IStringNode n : filteredList){
                        if (n.containsOffset(start))
                            isContained = true;
                    }
                    if (!isContained)
                        filteredList.add(stringNode);
                }
            }
        }
        
        return filteredList;
    }
    
    /**
     * Check if it is needed to check for non fully qualified access to static methods or fields.
     * Possible if the class with the element to be moved is imported by or in the same package
     * as the class for which the JML changes are computed.
     * @return true if non fully qualified access, i.e. ClassName.field, is possible.
     */
    private boolean checkForNonFullyQualified() {
        
        int lastPoint = oldClassFullQualName.lastIndexOf('.');
        String packageOldClass = oldClassFullQualName.substring(0, lastPoint);
        String oldClassName = oldClassFullQualName.substring(lastPoint+1);
        
        // Non fully qualified references are possible of if the (old) class with the field being moved is imported
        IImportDeclaration oldClassImported = compUnit.getImport(oldClassFullQualName);
        IImportDeclaration packageOldClassFullyImported = compUnit.getImport(packageOldClass+".*");
        if (oldClassImported.exists())
            return true;
        
        // if the wildcard import * is used, we need additionally check if the a class with same
        // name is in the same package. Then this is used first.
        if (packageOldClassFullyImported.exists()){
            try {
                IPackageFragment pack = (IPackageFragment) compUnit.getParent();
                IJavaElement[] elementsInPackage = pack.getChildren();
                for (IJavaElement ele : elementsInPackage){
                    if (ele.getElementType() == IJavaElement.COMPILATION_UNIT){
                        String elementName = ele.getElementName();
                        // remove the .java from Classname.java
                        String className = elementName.substring(0, elementName.lastIndexOf('.'));
                        if (className.equals(oldClassName))
                            return false;
                    }
                }
                // we have not found any class with the same name of the class to be moved in the package
                return true;
            }
            catch (JavaModelException e) {
                return false;
            }   
        }
        
        // Non fully qualified references might be possible if 
        // the (old) class is in the same package as the class for which changes are computed 
        String packageUnit;
        try {
            IPackageDeclaration[] packages = compUnit.getPackageDeclarations();
            if (packages.length > 0){
                packageUnit = packages[0].getElementName();
                
                // Is in same class -> Check if some other Class with the same name as the old class is imported
                if (packageOldClass.equals(packageUnit)){
                    
                   IImportDeclaration[] allImports = compUnit.getImports();
                   for (IImportDeclaration declaration : allImports){
                       String importStatement = declaration.getElementName();
                       String importedClass = importStatement.substring(importStatement.lastIndexOf('.')+1);
                       if (importedClass.equals(oldClassName)){
                           return false;
                       }
                   }
                   // In same package (no import needed) and no other class with same name imported
                   return true;

                }
            }      
        }
        catch (JavaModelException e) {
            return false;
        }
        
        return false;
    }

    /**
     * Creates the text change and adds it to changesToMake.
     * 
     * @param changesToMake list to add the {@link ReplaceEdit}s to.
     * @param node {@link IASTNode} to compute the change for.
     */
    protected final void computeReplaceEdit(ICompilationUnit unit, ArrayList<ReplaceEdit> changesToMake,
            IASTNode node) {

        final int startOffset = node.getStartOffset();
        
        // check if it is fully qualified
        String newClassName = newClassFullQualName.substring(newClassFullQualName.lastIndexOf('.')+1);
        String oldClassName = oldClassFullQualName.substring(oldClassFullQualName.lastIndexOf('.')+1);

        IASTNode innerNode = node.getChildren().get(0).getChildren().get(0);
        if (innerNode instanceof IStringNode && 
                ((IStringNode) innerNode).getString().equals(oldClassName)) {
            changesToMake.add(new ReplaceEdit(startOffset, oldClassName.length(), newClassName));
        }
        else {
            final int length = oldClassFullQualName.length();
            changesToMake.add(new ReplaceEdit(startOffset, length, newClassFullQualName));
        }
    }
}
