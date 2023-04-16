package de.uka.ilkd.key.java;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public class JPContext {
    private final ClassOrInterfaceDeclaration classContext;
    private final CompilationUnit cu;

    public JPContext(CompilationUnit cu, ClassOrInterfaceDeclaration classContext) {
        this.cu = cu;
        this.classContext = classContext;
    }

    public CompilationUnit getCompilationUnitContext() {
        return cu;
    }

    public ClassOrInterfaceDeclaration getClassDeclaration() {
        return classContext;
    }
}
