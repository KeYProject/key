/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.Iterator;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.expression.Assignment;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.LoopSpecification;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.collection.Pair;

public class BasicLoopExecutionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        ImmutableList<JTerm> posts = ImmutableSLList.nil();
        if (poVars.post.self != null) {
            posts = posts.append(d.tb.equals(poVars.post.self, poVars.pre.self));
        }

        if (poVars.pre.guard != null) {
            final JavaBlock guardJb = buildJavaBlock(d).second;
            posts =
                posts.append(d.tb.box(guardJb, d.tb.equals(poVars.post.guard, d.origVars.guard)));
        }
        Iterator<JTerm> localVars = d.origVars.localVars.iterator();
        Iterator<JTerm> localVarsAtPost = poVars.post.localVars.iterator();
        while (localVars.hasNext()) {
            JTerm i = localVars.next();
            JTerm o = localVarsAtPost.next();
            if (i != null && o != null) {
                posts = posts.append(d.tb.equals(o, i));
            }
        }
        posts = posts.append(d.tb.equals(poVars.post.heap, d.tb.getBaseHeap()));

        return buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
    }

    private JTerm buildProgramTerm(BasicSnippetData d, ProofObligationVars vs, JTerm postTerm,
            TermBuilder tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "program-term for a loop without modality.");
        }
        // create java block
        JModality.JavaModalityKind kind =
            (JModality.JavaModalityKind) d.get(BasicSnippetData.Key.MODALITY);
        final Pair<JavaBlock, JavaBlock> jb = buildJavaBlock(d);

        // create program term
        final JModality.JavaModalityKind symbExecMod;
        if (kind == JModality.JavaModalityKind.BOX) {
            symbExecMod = JModality.JavaModalityKind.DIA;
        } else {
            symbExecMod = JModality.JavaModalityKind.BOX;
        }
        final JTerm guardPreTrueTerm = d.tb.equals(vs.pre.guard, d.tb.TRUE());
        final JTerm guardPreFalseTerm = d.tb.equals(vs.pre.guard, d.tb.FALSE());
        final JTerm guardPreEqTerm = d.tb.equals(d.origVars.guard, vs.pre.guard);
        final JTerm bodyTerm = tb.prog(symbExecMod, jb.first, postTerm);
        final JTerm guardTrueBody = d.tb.imp(guardPreTrueTerm, bodyTerm);
        final JTerm guardFalseBody = d.tb.imp(guardPreFalseTerm, postTerm);
        final JTerm guardPreAndTrueTerm =
            tb.prog(kind, jb.second, tb.and(guardPreEqTerm, guardTrueBody));
        final JTerm programTerm = d.tb.and(guardPreAndTrueTerm, guardFalseBody);

        // create update
        JTerm update = tb.skip();
        Iterator<JTerm> paramIt = vs.pre.localVars.iterator();
        Iterator<JTerm> origParamIt = d.origVars.localVars.iterator();
        while (paramIt.hasNext()) {
            JTerm paramUpdate = d.tb.elementary(origParamIt.next(), paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }
        if (vs.post.self != null) {
            JTerm selfUpdate = d.tb.elementary(d.origVars.self, vs.pre.self);
            update = tb.parallel(selfUpdate, update);
        }
        return tb.apply(update, programTerm);
    }

    private Pair<JavaBlock, JavaBlock> buildJavaBlock(BasicSnippetData d) {
        ExecutionContext context = (ExecutionContext) d.get(BasicSnippetData.Key.EXECUTION_CONTEXT);

        // create loop call
        LoopSpecification inv = (LoopSpecification) d.get(BasicSnippetData.Key.LOOP_INVARIANT);
        StatementBlock sb = (StatementBlock) inv.getLoop().getBody();

        final Assignment guardVarDecl = new CopyAssignment((LocationVariable) d.origVars.guard.op(),
            inv.getLoop().getGuardExpression());
        final Statement guardVarMethodFrame = context == null ? guardVarDecl
                : new MethodFrame(null, context, new StatementBlock(guardVarDecl));

        // create java block
        final JavaBlock guardJb =
            JavaBlock.createJavaBlock(new StatementBlock(guardVarMethodFrame));
        final Statement s = new MethodFrame(null, context, sb);
        final JavaBlock res = JavaBlock.createJavaBlock(new StatementBlock(s));

        return new Pair<>(res, guardJb);
    }
}
