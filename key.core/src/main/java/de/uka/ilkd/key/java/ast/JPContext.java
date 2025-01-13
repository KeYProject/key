/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.body.ClassOrInterfaceDeclaration;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public record JPContext(ClassOrInterfaceDeclaration classContext, CompilationUnit cu) { }
