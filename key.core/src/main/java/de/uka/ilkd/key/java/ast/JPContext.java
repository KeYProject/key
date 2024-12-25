package de.uka.ilkd.key.java.ast;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public record JPContext(ClassOrInterfaceDeclaration classContext, CompilationUnit cu) { }
