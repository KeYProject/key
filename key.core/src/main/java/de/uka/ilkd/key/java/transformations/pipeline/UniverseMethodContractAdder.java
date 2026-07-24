/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.Arrays;
import java.util.List;

import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd;
import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.LabeledParserRuleContext;

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

import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.ACCESSIBLE;
import static de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase.ClauseHd.ASSIGNABLE_FREE;

public class UniverseMethodContractAdder extends JavaTransformerAbstract {
    public final static Logger LOGGER = LoggerFactory.getLogger(UniverseMethodContractAdder.class);

    public final static String[] OWNERSHIP = new String[] { "Rep", "Peer", "Dom" };
    public final static String[] REPONLY = new String[] { "RepOnly" };

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
                if (returnT.isVoidType())
                    returnT = null;

                returnAnnot = filterAnnots(meth.getAnnotations(), OWNERSHIP);
                isRepOnly = filterAnnots(meth.getAnnotations(), REPONLY) != null;
                params = meth.getParameters();
            }

            if (it instanceof ConstructorDeclaration cons) {
                isRepOnly = filterAnnots(cons.getAnnotations(), REPONLY) != null;
                params = cons.getParameters();
            }

            List<TextualJMLConstruct> specList = TransformationPipelineServices.getSpec(it);
            for (TextualJMLConstruct spec : specList) {
                if (!(spec instanceof TextualJMLSpecCase))
                    continue;
                var sc = (TextualJMLSpecCase) spec;

                if (isRepOnly) {
                    var context = new LabeledParserRuleContext(
                        JmlFacade.parseExpr("\\dl_createdRepfp(this)"));
                    sc.addClause(ASSIGNABLE_FREE, null, context);

                    if (returnT != null) {
                        sc.addClause(ACCESSIBLE, null, context);
                    }
                }

                if (returnAnnot != null) {
                    sc.addClause(ClauseHd.ENSURES_FREE,
                        getOwnershipContext("\\result", returnAnnot));
                }

                for (Parameter param : params) {
                    AnnotationExpr annot = filterAnnots(param.annotations(), OWNERSHIP);
                    if (annot == null)
                        continue;
                    sc.addClause(ClauseHd.REQUIRES_FREE,
                        getOwnershipContext(param.getNameAsString(), annot));
                }
            }
        });
    }

    private static LabeledParserRuleContext getOwnershipContext(String varName,
            AnnotationExpr annot) {
        String fstring = annot.getNameAsString().equals("Rep")
                ? "%1$s != null ==> this == \\dl_owner(%1$s)"
                : annot.getNameAsString().equals("Peer")
                        ? "%1$s != null ==> \\dl_owner(this) == \\dl_owner(%1$s)"
                        : "%1$s != null ==> \\dl_dominates(this, %1$s)";
        String expr = String.format(fstring, varName);
        return new LabeledParserRuleContext(JmlFacade.parseExpr(expr));
    }

    private static AnnotationExpr filterAnnots(NodeList<AnnotationExpr> annots, String[] allowed) {
        if (annots == null)
            return null;
        return annots.stream()
                .filter(annot -> Arrays.stream(allowed)
                        .anyMatch(val -> annot.getName().toString().equals(val)))
                .findFirst()
                .orElse(null);
    }
}
