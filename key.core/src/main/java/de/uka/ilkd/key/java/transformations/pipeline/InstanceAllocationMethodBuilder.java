/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
// Technical University Darmstadt, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.type.ClassOrInterfaceType;

/**
 * creates a method declaration with no implementation. The methods intention is
 * to allocate a new object of the type it is declared in and to return it.
 * The functionality will be described using taclets
 */
public class InstanceAllocationMethodBuilder extends JavaTransformer {

    public InstanceAllocationMethodBuilder(TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(CompilationUnit cu) {
        super.apply(cu);
    }

    @Override
    public void apply(TypeDeclaration<?> td) {
        if (td.isRecordDeclaration() || td.isClassOrInterfaceDeclaration()) {
            MethodDeclaration md = td.addMethod(PipelineConstants.IMPLICIT_INSTANCE_ALLOCATE,
                Modifier.Keyword.PUBLIC, Modifier.Keyword.STATIC);
            md.setBody(null);
            md.setType(new ClassOrInterfaceType(null, td.getName(), null));
        }
    }

}
