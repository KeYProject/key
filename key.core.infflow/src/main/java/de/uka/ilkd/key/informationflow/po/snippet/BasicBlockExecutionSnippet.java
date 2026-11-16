/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.informationflow.po.snippet;

import java.util.Iterator;

import de.uka.ilkd.key.informationflow.ProofObligationVars;
import de.uka.ilkd.key.java.ast.Label;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.StatementBlock;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.JModality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.AuxiliaryContractBuilders;
import de.uka.ilkd.key.speclang.AuxiliaryContract;

import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NullMarked;


/**
 *
 * @author christoph
 */
@NullMarked
class BasicBlockExecutionSnippet extends ReplaceAndRegisterMethod implements FactoryMethod {

    @Override
    public JTerm produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        ImmutableList<JTerm> posts = ImmutableList.nil();
        if (poVars.post.self != null && poVars.pre.self != null) {
            posts = posts.append(d.tb.equals(poVars.post.self, poVars.pre.self));
        }
        Iterator<JTerm> localVars = d.origVars.localVars.iterator();
        Iterator<JTerm> localPostVars = poVars.post.localVars.iterator();
        while (localVars.hasNext()) {
            posts = posts.append(d.tb.equals(localPostVars.next(), localVars.next()));
        }
        if (poVars.post.result != null && poVars.pre.result != null) {
            posts = posts.append(d.tb.equals(poVars.post.result, poVars.pre.result));
        }
        if (poVars.pre.exception != null && poVars.post.exception != null) {
            posts = posts.append(d.tb.equals(poVars.post.exception, poVars.pre.exception));
        }
        posts = posts.append(d.tb.equals(poVars.post.heap, d.tb.getBaseHeap()));
        final JTerm prog = buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
        return prog;
    }

    private JTerm buildProgramTerm(BasicSnippetData d, ProofObligationVars vs, JTerm postTerm,
            TermBuilder tb) {
        final Object modalityObj = d.get(BasicSnippetData.Key.MODALITY);
        if (modalityObj == null) {
            throw new UnsupportedOperationException(
                "Tried to produce a " + "program-term for a " + "contract without modality.");
        }

        // create java block
        final JModality.JavaModalityKind kind = (JModality.JavaModalityKind) modalityObj;
        final JavaBlock jb = buildJavaBlock(d, vs);

        // create program term
        final JModality.JavaModalityKind symbExecMod;
        if (kind == JModality.JavaModalityKind.BOX) {
            symbExecMod = JModality.JavaModalityKind.DIA;
        } else {
            symbExecMod = JModality.JavaModalityKind.BOX;
        }
        final JTerm programTerm = tb.prog(symbExecMod, jb, postTerm);

        // create update
        JTerm update = tb.skip();
        Iterator<JTerm> paramIt = vs.pre.localVars.iterator();
        Iterator<JTerm> origParamIt = d.origVars.localVars.iterator();
        while (paramIt.hasNext()) {
            JTerm paramUpdate = d.tb.elementary(origParamIt.next(), paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }
        if (vs.post.self != null && vs.pre.self != null) {
            final Object blockSelfObj = d.get(BasicSnippetData.Key.BLOCK_SELF);
            if (blockSelfObj == null) {
                throw new NullPointerException(
                    "No self term of the transformed block contract.");
            }
            final JTerm selfTerm = (JTerm) blockSelfObj;
            final JTerm selfUpdate = d.tb.elementary(selfTerm, vs.pre.self);
            update = tb.parallel(selfUpdate, update);
        }
        return tb.apply(update, programTerm);
    }


    private JavaBlock buildJavaBlock(BasicSnippetData d, ProofObligationVars poVars) {
        final ExecutionContext context =
            (ExecutionContext) d.get(BasicSnippetData.Key.EXECUTION_CONTEXT);
        if (context == null) {
            throw new NullPointerException(
                "No execution context for the block symbolic execution block.");
        }
        final ProgramVariable exceptionParameter =
            poVars.exceptionParameter.op(ProgramVariable.class);

        // create block call
        final Object labelsObj = d.get(BasicSnippetData.Key.LABELS);
        if (labelsObj == null) {
            throw new NullPointerException("No labels for the block symbolic execution block.");
        }
        final Label[] labelsArray = (Label[]) labelsObj;
        final ImmutableArray<Label> labels = new ImmutableArray<>(labelsArray);
        final Object variablesObj = d.get(BasicSnippetData.Key.BLOCK_VARS);
        if (variablesObj == null) {
            throw new NullPointerException(
                "No block contract variables for the block symbolic execution block.");
        }
        final AuxiliaryContract.Variables variables = (AuxiliaryContract.Variables) variablesObj;
        final Object blockObj = d.get(BasicSnippetData.Key.TARGET_BLOCK);
        if (blockObj == null) {
            throw new NullPointerException(
                "No target block for the block symbolic execution block.");
        }
        final StatementBlock block = (StatementBlock) blockObj;
        final StatementBlock sb = new AuxiliaryContractBuilders.ValidityProgramConstructor(labels,
            block, variables, exceptionParameter, d.services).construct();
        final Statement s = new MethodFrame(null, context, sb);
        final JavaBlock result = JavaBlock.createJavaBlock(new StatementBlock(s));

        return result;
    }
}
