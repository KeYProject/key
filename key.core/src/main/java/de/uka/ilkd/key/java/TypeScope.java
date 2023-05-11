package de.uka.ilkd.key.java;


import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

/**
 * The property of a non terminal program element to define a scope for types. taken from COMPOST
 * and changed to achieve an immutable structure
 */

public interface TypeScope extends ScopeDefiningElement {

    /**
     * @author Alexander Weigl
     * @version 1 (05.03.22)
     */
    class JPContext {
        private final ClassOrInterfaceDeclaration classContext;
        private final com.github.javaparser.ast.CompilationUnit cu;

        public JPContext(com.github.javaparser.ast.CompilationUnit cu,
                ClassOrInterfaceDeclaration classContext) {
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
}
