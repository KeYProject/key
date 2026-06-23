/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.AnnotationExpr;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class UniverseMethodContractAdder extends JavaTransformerAbstract {
    public final static Logger LOGGER = LoggerFactory.getLogger(UniverseMethodContractAdder.class);

    public UniverseMethodContractAdder(@NonNull TransformationPipelineServices services) {
        super(services);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(it -> {
            if (it instanceof MethodDeclaration meth) {
                if (meth.name().toString().startsWith("$"))
                    return;
                LOGGER.info("found method {} with annotations {}, params {}, type {}",
                    meth.name(), meth.annotations(), meth.getParameters(), meth.getType());
            }

            if (it instanceof ConstructorDeclaration cons) {
                // TODO: do that next
            }
        });
    }


    private AnnotationExpr getReturnAnnotation(NodeList<AnnotationExpr> annotations) {
        return null;
    }
}
