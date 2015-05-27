package org.key_project.jmlediting.ui.outlineView;

import org.eclipse.jdt.core.ICompilationUnit;
import org.key_project.javaeditor.outline.OutlineCompilationUnitWrapper;

public class OutlineCompilationUnitWrapperExtension extends
        OutlineCompilationUnitWrapper {

    public OutlineCompilationUnitWrapperExtension(ICompilationUnit wrappedObject) {
        super(wrappedObject);
        System.out.println("CONSTREKTETRR CALLD");
        // TODO Auto-generated constructor stub
    }

}
