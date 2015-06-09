package org.key_project.jmlediting.ui.outlineView;

import java.io.InputStream;
import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.jobs.ISchedulingRule;
import org.eclipse.jdt.core.CompletionRequestor;
import org.eclipse.jdt.core.IAnnotation;
import org.eclipse.jdt.core.IClassFile;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.ICompletionRequestor;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IInitializer;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaModel;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IOpenable;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.ITypeHierarchy;
import org.eclipse.jdt.core.ITypeParameter;
import org.eclipse.jdt.core.ITypeRoot;
import org.eclipse.jdt.core.IWorkingCopy;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.WorkingCopyOwner;
import org.key_project.javaeditor.outline.DefaultOutlineModifiyer;
import org.key_project.javaeditor.outline.IOutlineWrapper;
import org.key_project.javaeditor.outline.OutlineTypeWrapper;
import org.key_project.javaeditor.util.LogUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;

public class TestOutlineExtension extends DefaultOutlineModifiyer {
   @Override
   public IJavaElement[] modify(IJavaElement parent, IJavaElement[] currentChildren) {
      List<IJavaElement> newChildrenList = new ArrayList<IJavaElement>();    
            
      for(IJavaElement child: currentChildren) {
         if(child.getElementType() == IJavaElement.TYPE) {
            OutlineTypeWrapper cast = (OutlineTypeWrapper) child; 
            newChildrenList.add(cast);
         } else {
            newChildrenList.add(child);
         }
      }
      
      IJavaElement[] array = new IJavaElement[1];
      array = newChildrenList.toArray(array);
      
      return array;
   }
}
