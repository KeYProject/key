/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof_references.analyst;

import java.util.LinkedHashSet;

import de.uka.ilkd.key.java.JavaTools;
import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof_references.ProofReferenceUtil;
import de.uka.ilkd.key.proof_references.reference.DefaultProofReference;
import de.uka.ilkd.key.proof_references.reference.IProofReference;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableSLList;

/**
 * Extracts called methods.
 *
 * @author Martin Hentschel
 */
public class MethodCallProofReferencesAnalyst implements IProofReferencesAnalyst {
    /**
     * {@inheritDoc}
     */
    @Override
    public LinkedHashSet<IProofReference<?>> computeReferences(Node node, Services services) {
        String name = MiscTools.getRuleName(node);
        if (name != null && name.toLowerCase().contains("methodcall")) {
            NodeInfo info = node.getNodeInfo();
            if (info != null) {
                if (info.getActiveStatement() instanceof MethodReference) {
                    ExecutionContext context = extractContext(node, services);
                    IProofReference<IProgramMethod> reference = createReference(node, services,
                        context, (MethodReference) info.getActiveStatement());
                    LinkedHashSet<IProofReference<?>> result =
                        new LinkedHashSet<>();
                    result.add(reference);
                    return result;
                } else if (info.getActiveStatement() instanceof Assignment assignment) {
                    ExecutionContext context = extractContext(node, services);
                    LinkedHashSet<IProofReference<?>> result =
                        new LinkedHashSet<>();
                    for (int i = 0; i < assignment.getChildCount(); i++) {
                        ProgramElement child = assignment.getChildAt(i);
                        if (child instanceof MethodReference) {
                            IProofReference<IProgramMethod> reference =
                                createReference(node, services, context, (MethodReference) child);
                            ProofReferenceUtil.merge(result, reference);
                        }
                    }
                    return result;
                } else {
                    return null;
                }
            } else {
                return null;
            }
        } else {
            return null;
        }
    }

    /**
     * Extracts the {@link ExecutionContext}.
     *
     * @param node The {@link Node} to extract {@link ExecutionContext} from.
     * @param services The {@link Services} to use.
     * @return The found {@link ExecutionContext} or {@code null} if not available.
     */
    protected ExecutionContext extractContext(Node node, Services services) {
        RuleApp app = node.getAppliedRuleApp();
        PosInOccurrence pio = app.posInOccurrence();
        JavaBlock jb = TermBuilder.goBelowUpdates((JTerm) pio.subTerm()).javaBlock();
        return JavaTools.getInnermostExecutionContext(jb, services);
    }

    /**
     * Creates an {@link IProofReference} to the called {@link IProgramMethod}.
     *
     * @param node The {@link Node} which caused the reference.
     * @param services The {@link Services} to use.
     * @param context The {@link ExecutionContext} to use.
     * @param mr The {@link MethodReference}.
     * @return The created {@link IProofReference}.
     */
    protected IProofReference<IProgramMethod> createReference(Node node, Services services,
            ExecutionContext context, MethodReference mr) {
        if (context != null) {
            KeYJavaType refPrefixType = mr.determineStaticPrefixType(services, context);
            IProgramMethod pm = mr.method(services, refPrefixType, context);
            return new DefaultProofReference<>(IProofReference.CALL_METHOD, node, pm);
        } else {
            if (!(node.getAppliedRuleApp() instanceof PosTacletApp app)) {
                throw new IllegalArgumentException("PosTacletApp expected.");
            }
            if (!"staticMethodCallStaticWithAssignmentViaTypereference"
                    .equals(MiscTools.getRuleName(node))) {
                throw new IllegalArgumentException(
                    "Rule \"staticMethodCallStaticWithAssignmentViaTypereference\" expected, but is \""
                        + MiscTools.getRuleName(node) + "\".");
            }
            SchemaVariable methodSV = app.instantiations().lookupVar(new Name("#mn"));
            SchemaVariable typeSV = app.instantiations().lookupVar(new Name("#t"));
            SchemaVariable argsSV = app.instantiations().lookupVar(new Name("#elist"));

            ProgramElementName method =
                (ProgramElementName) app.instantiations().getInstantiation(methodSV);
            TypeRef type = (TypeRef) app.instantiations().getInstantiation(typeSV);
            ImmutableArray<?> args =
                (ImmutableArray<?>) app.instantiations().getInstantiation(argsSV);
            if (!args.isEmpty()) {
                throw new IllegalArgumentException("Empty argument list expected.");
            }
            IProgramMethod pm = services.getJavaInfo().getProgramMethod(type.getKeYJavaType(),
                method.toString(), ImmutableSLList.nil(), type.getKeYJavaType());
            return new DefaultProofReference<>(IProofReference.CALL_METHOD, node, pm);
        }
    }
}
