/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.Arrays;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.type.Type;
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
            if (!(it instanceof MethodDeclaration ||
                    it instanceof ConstructorDeclaration))
                return;

            Type returnT = null;
            AnnotationExpr returnAnnot = null;
            boolean isRepOnly = false;
            NodeList<Parameter> params = null;

            if (it instanceof MethodDeclaration meth) {
                returnT = meth.getType();
                returnAnnot = filterAnnots(
                    meth.getAnnotations(), new String[] { "Rep", "Peer", "Dom" });
                isRepOnly = filterAnnots(
                    meth.getAnnotations(), new String[] { "RepOnly" }) != null;
                params = meth.getParameters();
            }

            if (it instanceof ConstructorDeclaration cons) {
                isRepOnly = filterAnnots(
                    cons.getAnnotations(), new String[] { "RepOnly" }) != null;
                params = cons.getParameters();
            }

            var spec = TransformationPipelineServices.getSpec(it);
            LOGGER.info("return type {} {}", returnAnnot, returnT);
            LOGGER.info("repOnly {}", isRepOnly);
            LOGGER.info("params {}", params);
        });
    }

    private static AnnotationExpr filterAnnots(NodeList<AnnotationExpr> annnots, String[] allowed) {
        return annnots.stream()
                .filter(annot -> Arrays.stream(allowed)
                        .anyMatch(val -> annot.getName().toString().equals(val)))
                .findFirst()
                .orElse(null);
    }
}
