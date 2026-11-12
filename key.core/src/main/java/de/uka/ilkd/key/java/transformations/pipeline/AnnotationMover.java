/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Java Annotations can be attached to different constructs, such as
 * type uses or variable declarations. This means that when parsing
 * an annotated declaration like <code> @NonNull Object o; <code/>
 * it is ambigous wether @NonNull should be attached to the type
 * Object or to the whole declaration.
 *
 * The solution for this are @Target meta annotations, that specify
 * the construct the annotation gets attached to. The @Target annotations
 * are not read by the parser though. Which means that all annotations
 * are attached to the declaration even if the type would have been
 * the target.
 *
 * This Transformation tries to find the annotation declaration
 * and moves the annotation from the declaration to the type
 * if the declaration has the correct @Target annotation.
 *
 * @author Daniel Grévent
 */
public class AnnotationMover extends JavaTransformerAbstract {
    private static final Logger LOGGER = LoggerFactory.getLogger(AnnotationMover.class);

    /// a mapping from annotation names to whether or not they are type annotations
    final Map<String, Boolean> typeAnnotationMap = new LinkedHashMap<>();

    public AnnotationMover(TransformationPipelineServices pipelineServices) {
        super(pipelineServices);
    }

    @Override
    public void apply(CompilationUnit cu) {
        cu.walk(MethodDeclaration.class,
            it -> move(it.annotations(), it.getType()));
        cu.walk(Parameter.class,
            it -> move(it.annotations(), it.getType()));
        cu.walk(VariableDeclarator.class, it -> {
            var d = (VariableDeclarator) it;
            Node parent = d.getParentNode().get();
            NodeList<AnnotationExpr> annots = null;
            switch (parent) {
                case FieldDeclaration f:
                    annots = f.getAnnotations();
                    break;
                case VariableDeclarationExpr v:
                    annots = v.getAnnotations();
                    break;
                default:
                    LOGGER.error("unexpected class: {}", parent.getClass());
                    break;
            }

            move(annots, d.getType());
        });
    }

    private void move(NodeList<AnnotationExpr> declList, Type type) {
        if (declList == null)
            return;

        Iterator<AnnotationExpr> iter = declList.iterator();
        while (iter.hasNext()) {
            AnnotationExpr annot = iter.next();
            if (!isTypeAnnotation(annot)) {
                continue;
            }

            // remove the annotation from the declaration
            // and move it to the type
            iter.remove();
            annot.setParentNode(type);
            type.annotations().add(annot);
        }
    }

    private boolean isTypeAnnotation(AnnotationExpr annot) {
        String name = annot.getNameAsString(); //
        if (typeAnnotationMap.containsKey(name)) {
            return typeAnnotationMap.get(name);
        }

        boolean result = isTypeAnnotationSlow(annot);
        typeAnnotationMap.put(name, result);
        return result;
    }

    private boolean isTypeAnnotationSlow(AnnotationExpr annot) {
        ResolvedAnnotationDeclaration resolved;
        try {
            resolved = annot.resolve();
        } catch (Exception ex) {
            return false;
        }

        var decl = (AnnotationDeclaration) resolved.toAst().get();
        for (AnnotationExpr subAnnot : decl.annotations()) {
            if (!subAnnot.getNameAsString().equals("Target")) {
                continue;
            }

            if (!(subAnnot instanceof SingleMemberAnnotationExpr)) {
                return false;
            }

            var value = ((SingleMemberAnnotationExpr) subAnnot).getMemberValue();
            if (value.toString().contains("TYPE_USE")) {
                return true;
            }

            break;
        }

        return false;
    }
}
