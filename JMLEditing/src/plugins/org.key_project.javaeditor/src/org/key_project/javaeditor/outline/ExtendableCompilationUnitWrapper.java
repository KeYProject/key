package org.key_project.javaeditor.outline;

import java.util.WeakHashMap;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.javaeditor.util.ExtendableOutlineUtil;

public class ExtendableCompilationUnitWrapper extends OutlineCompilationUnitWrapper {
    private final WeakHashMap<IJavaElement, IJavaElement> wrapper2extendedMap = new WeakHashMap<IJavaElement, IJavaElement>();

    private final IOutlineModifier[] modify = ExtendableOutlineUtil.createEnabledJavaExtensions();
    
    public ExtendableCompilationUnitWrapper(ICompilationUnit wrappedObject) {
        super(wrappedObject);
    }

    @Override
    public IJavaElement[] getChildren() throws JavaModelException {
       // TODO: Define an extension point and API to extend and modify the children shown in the oultine. Realize the extension point for JML in plug-in org.key_project.jmlediting.ui.
       IJavaElement[] children = getWrappedObject().getChildren();
       // Make children extendable
       IJavaElement[] modifyableChildren = new IJavaElement[children.length];
       for (int i = 0; i < children.length; i++) {
           modifyableChildren[i] = wrapper2extendedMap.get(children[i]);
           if (modifyableChildren[i] == null) {
               // TODO: Extenadble java element wrapper, pass modify
               if (children[i] instanceof IType) {
                  modifyableChildren[i] = new OutlineTypeWrapper((IType)children[i]);
               }
               else if (children[i] instanceof ICompilationUnit) {
                  modifyableChildren[i] = new OutlineCompilationUnitWrapper((ICompilationUnit)children[i]);
               }
               else {
                  modifyableChildren[i] = new OutlineJavaElementWrapper<IJavaElement>(children[i]);
               }
               wrapper2extendedMap.put(children[i], modifyableChildren[i]);
           }
       }
       // Allow modifier to change children
       for (IOutlineModifier modifyer : modify) {
           modifyableChildren = modifyer.modify(getWrappedObject(), modifyableChildren);
       }
       
       return modifyableChildren;
    }

}
