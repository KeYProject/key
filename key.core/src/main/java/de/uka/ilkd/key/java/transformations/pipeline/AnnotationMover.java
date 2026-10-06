/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.AnnotationDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AnnotationExpr;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;
import com.github.javaparser.ast.expr.SingleMemberAnnotationExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.declarations.ResolvedAnnotationDeclaration;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This transformation moves type annotations to their type from the corresponding declaration.
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
            var d = (VariableDeclarator)it;
            Node parent = d.getParentNode().get();
            NodeList<AnnotationExpr> annots = null;
            switch (parent) {
                case FieldDeclaration f: annots = f.getAnnotations(); break;
                case VariableDeclarationExpr v: annots = v.getAnnotations(); break;
                default: 
                    LOGGER.error("unexpected class: {}", parent.getClass());
                    break;
            }

            move(annots, d.getType());
        });
    }

    private void move(NodeList<AnnotationExpr> declList, Type type) {
        if (declList == null) return;

        Iterator<AnnotationExpr> iter = declList.iterator();
        while (iter.hasNext()) {
            AnnotationExpr annot = iter.next();
            if (!isTypeAnnotation(annot)) continue;
            iter.remove();
            annot.setParentNode(type);
            type.annotations().add(annot);
        }
    }

    private boolean isTypeAnnotation(AnnotationExpr annot) {
        String name = annot.getNameAsString();
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

        var decl = (AnnotationDeclaration)resolved.toAst().get();
        for (AnnotationExpr subAnnot : decl.annotations()) {
            if (!subAnnot.getNameAsString().equals("Target")) continue;
            if (!(subAnnot instanceof SingleMemberAnnotationExpr)) return false;
            var array = ((SingleMemberAnnotationExpr)subAnnot).getMemberValue();
            if (!(array instanceof ArrayInitializerExpr)) return false;
            
            for (var value : ((ArrayInitializerExpr)array).getValues()) {
                if (value.toString().equals("ElementType.TYPE_USE")) return true;
            }

            break;
        }

        return false;
    }
}
