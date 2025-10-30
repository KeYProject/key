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

import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.ThisExpr;

/**
 * Local and anonymous classes may access variables from the creating context
 * if they are declared final and initialised.
 * <p>
 * This transformation searches for such final variables and replaces them by
 * an implicit variable.
 * <p>
 * Additionally a pseudo name is assigned to anonymous classes to allow to
 * access them despite all.
 *
 * @author engelc
 */
public class LocalClassTransformation extends JavaTransformer {

    public LocalClassTransformation(TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(TypeDeclaration<?> td) {
        var outerVars = services.getFinalVariables(td);
        if (outerVars != null) {
            for (var v : outerVars) {
                for (final var vr : services.getUsages(v, td)) {
                    FieldAccessExpr fr = new FieldAccessExpr(new ThisExpr(),
                        PipelineConstants.FINAL_VAR_PREFIX + v.getName());
                    // TODO javaparser td.replace(vr, fr);
                }
            }
        }
    }

}
