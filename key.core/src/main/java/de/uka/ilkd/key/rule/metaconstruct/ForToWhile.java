/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.rule.metaconstruct;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.statement.EnhancedFor;
import de.uka.ilkd.key.java.ast.statement.LoopStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.java.visitor.ProgVarReplaceVisitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * converts a for-loop to a while loop. Invariant and other rules cannot be performed on for but
 * only on while loops.
 *
 * It makes uses of the {@link ForToWhileTransformation} to create a transformed loop body which is
 * then put into the corresponding context.
 *
 * <h2>Example</h2>
 *
 * <pre>
 * for (int i = 0; i &lt; 100; i++) {
 *     if (i == 2)
 *         continue;
 *     if (i == 3)
 *         break;
 * }
 * </pre>
 *
 * is translated to
 *
 * <pre>
 * _label1: {
 *     int i = 0;
 *     while (i &lt; 100) {
 *         _label0: {
 *             if (i == 2)
 *                 break _label0;
 *             if (i == 3)
 *                 break _label1;
 *         }
 *         i++;
 *     }
 * }
 * </pre>
 *
 * @see ForToWhileTransformation
 * @author MU
 */

@TransformerMeta(name = "#forToWhile")
public class ForToWhile extends ProgramTransformer {

    /**
     * the outer label that is used to leave the while loop ('l1')
     */
    private final SchemaVariable outerLabel;

    /**
     * the inner label ('l2')
     */
    private final SchemaVariable innerLabel;

    /**
     * creates an loop to while - ProgramTransformer
     *
     * @param loop the LoopStatement contained by the meta construct
     * @param innerLabel the label used to handle continue
     * @param outerLabel the label used to handle break (only needed for do-while-loops)
     */
    public ForToWhile(SchemaVariable innerLabel, SchemaVariable outerLabel, Statement loop) {
        super("#forToWhile", loop);
        this.innerLabel = innerLabel;
        this.outerLabel = outerLabel;

    }

    @Override
    public ImmutableList<ProgramElement> getArguments() {
        final ProgramElement inner = (ProgramElement) innerLabel;
        final ProgramElement outer = (ProgramElement) outerLabel;
        if (inner != null) {
            return outer == null ? ImmutableList.of(inner, body())
                    : ImmutableList.of(inner, outer, body());
        }
        return outer == null ? ImmutableList.of(body()) : ImmutableList.of(outer, body());
    }

    /**
     * Recovers the loop specification of a loop that lost its attached specification while it was
     * reconstructed from a taclet pattern. The pattern is re-parsed from text without JML, so the
     * specification has to be looked up in the original method declaration. Method-frame parameter
     * renaming adds a leading {@code _} to parameter names, which is ignored for the match.
     *
     * @param loop the loop whose specification is missing
     * @param svInst the current instantiations, used to find the enclosing method
     * @return the matching specification, or {@code null} if there is none or the match is
     *         ambiguous
     */
    private static @Nullable LoopSpecification findSourceLoopInvariant(
            LoopStatement loop,
            SVInstantiations svInst, Services services) {
        var context = svInst.getContextInstantiation();
        if (context == null || context.activeStatementContext() == null) {
            return null;
        }
        var method = context.activeStatementContext().getMethodContext();
        if (method == null || method.getMethodDeclaration() == null
                || method.getMethodDeclaration().getBody() == null) {
            return null;
        }

        String key = loopKey(loop);
        LoopStatement match = null;
        var collector = new JavaASTCollector(method.getMethodDeclaration().getBody(),
            LoopStatement.class);
        collector.start();
        for (var node : collector.getNodes()) {
            var candidate = (LoopStatement) node;
            if (candidate.getLoopInvariant() != null && loopKey(candidate).equals(key)) {
                if (match != null) {
                    return null;
                }
                match = candidate;
            }
        }
        if (match == null) {
            return null;
        }
        if (match.getLoopInvariant() != null) {
            return match.getLoopInvariant();
        }
        if (match.getExpandedLoopInvariant() != null) {
            return match.getExpandedLoopInvariant();
        }

        // The source loop still uses the source parameter names; the loop in the proof has
        // method-frame-renamed variables. Remap the specification through a fresh
        // ProgVarReplaceVisitor so the invariant is expressed over the proof's variables.
        Map<LocationVariable, LocationVariable> map = new LinkedHashMap<>();
        var sourceVariables = new JavaASTCollector(match, ProgramVariable.class);
        sourceVariables.start();
        var targetVariables = new JavaASTCollector(loop, ProgramVariable.class);
        targetVariables.start();
        for (var source : sourceVariables.getNodes()) {
            if (!(source instanceof LocationVariable sourceVariable)) {
                continue;
            }
            String sourceName = sourceVariable.name().toString().replaceFirst("^_", "");
            for (var target : targetVariables.getNodes()) {
                if (target instanceof LocationVariable targetVariable
                        && targetVariable.name().toString().replaceFirst("^_", "")
                                .equals(sourceName)) {
                    map.put(sourceVariable, targetVariable);
                    break;
                }
            }
        }
        var replacer = new ProgVarReplaceVisitor(match, map, services);
        replacer.start();
        return ((LoopStatement) replacer.result()).getLoopInvariant();
    }

    /**
     * Structural key of a loop that ignores the method-frame parameter renaming.
     */
    private static String loopKey(LoopStatement loop) {
        String guard =
            loop.getGuardExpression() == null ? "" : loop.getGuardExpression().toString();
        String body = loop.getBody() == null ? "" : loop.getBody().toString();
        return (guard + "|" + body).replaceAll("\\b_", "");
    }

    @Override
    public ProgramElement[] transform(ProgramElement pe, Services services,
            SVInstantiations svInst) {

        LoopSpecification sourceInvariant = null;
        ProgramVariable arraySource = null;
        Map<String, ProgramVariable> targetVariables = new LinkedHashMap<>();
        if (svInst.getContextInstantiation() != null
                && svInst.getContextInstantiation().activeStatementContext() != null) {
            if (svInst.getContextInstantiation().program() != null) {
                var prog = svInst.getContextInstantiation().program();
                var cols = new JavaASTCollector(prog, ProgramVariable.class);
                cols.start();
                for (var node : cols.getNodes()) {
                    var pv = (ProgramVariable) node;
                    targetVariables.put(pv.name().toString(), pv);
                }
            }
            var method =
                svInst.getContextInstantiation().activeStatementContext().getMethodContext();
            if (method != null && method.getBody() != null) {
                var collector = new JavaASTCollector(method.getBody(), EnhancedFor.class);
                collector.start();
                for (var node : collector.getNodes()) {
                    var inv = ((EnhancedFor) node).getLoopInvariant();
                    if (inv != null) {
                        if (sourceInvariant != null) {
                            sourceInvariant = null;
                            break;
                        }
                        sourceInvariant = inv;
                    }
                }
            }
        }
        if (sourceInvariant == null && pe instanceof LoopStatement loop
                && loop.getLoopInvariant() == null) {
            sourceInvariant = findSourceLoopInvariant(loop, svInst, services);
        }
        if (sourceInvariant != null
                && sourceInvariant.getLoop() instanceof EnhancedFor ef
                && ef.getGuardExpression() instanceof ProgramVariable pv) {
            arraySource = pv;
        }
        WhileLoopTransformation w = new ForToWhileTransformation(pe,
            (ProgramElementName) svInst.getInstantiation(outerLabel),
            (ProgramElementName) svInst.getInstantiation(innerLabel), services, sourceInvariant,
            targetVariables, arraySource);

        w.start();
        return new ProgramElement[] { w.result() };
    }

    /**
     * return a list of the SV that are relevant to this UnwindLoop
     *
     * @param svInst the instantiations so far - ignored
     * @return a list of 0 to 2 schema variables (outer/inner label)
     */
    @Override
    public ImmutableList<SchemaVariable> neededInstantiations(SVInstantiations svInst) {
        ImmutableList<SchemaVariable> ret = ImmutableList.nil();

        if (innerLabel != null) {
            ret = ret.prepend(innerLabel);
        }

        if (outerLabel != null) {
            ret = ret.prepend(outerLabel);
        }

        return ret;
    }
}
