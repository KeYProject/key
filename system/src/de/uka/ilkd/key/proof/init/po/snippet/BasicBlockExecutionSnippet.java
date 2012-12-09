package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.speclang.BlockContract.Variables;


/**
 *
 * @author christoph
 */
class BasicBlockExecutionSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d,
                        ProofObligationVars poVars)
            throws UnsupportedOperationException {
        ImmutableList<Term> posts = ImmutableSLList.<Term>nil();
        if (poVars.selfAtPost != null) {
            posts = posts.append(d.tb.equals(poVars.selfAtPost, poVars.self));
        }
        if (poVars.resultAtPost != null) {
            posts = posts.append(d.tb.equals(poVars.resultAtPost,
                                             poVars.result));
        }
        if (poVars.exception != null && poVars.exceptionAtPost != null) {
            posts = posts.append(d.tb.equals(poVars.exceptionAtPost,
                                             poVars.exception));
        }
        posts = posts.append(d.tb.equals(poVars.heapAtPost, poVars.heap));
        final Term prog = buildProgramTerm(d, d.tb.and(posts), d.tb);
        return prog;
    }

    private Term buildProgramTerm(BasicSnippetData d,
                                  Term postTerm,
                                  TermBuilder.Serviced tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException("Tried to produce a " +
                                                    "program-term for a contract without modality.");
        }

        //create java block
        Modality modality =
                (Modality) d.get(BasicSnippetData.Key.MODALITY);
        final JavaBlock jb = buildJavaBlock(d);

        //create program term
        final Modality symbExecMod;
        if (modality == Modality.BOX) {
            symbExecMod = Modality.DIA;
        } else {
            symbExecMod = Modality.BOX;
        }
        final Term programTerm = tb.prog(symbExecMod, jb, postTerm);

        return programTerm;
    }


    private JavaBlock buildJavaBlock(BasicSnippetData d) {
        Services services = d.tb.getServices();
        ExecutionContext context =
                (ExecutionContext) d.get(BasicSnippetData.Key.CONTEXT);

        //create block call
        Label[] labelsArray = (Label[]) d.get(BasicSnippetData.Key.LABELS);
        ImmutableArray<Label> labels = new ImmutableArray<Label>(labelsArray);
        Variables variables =
                (Variables) d.get(BasicSnippetData.Key.BLOCK_VARS);
        StatementBlock block =
                (StatementBlock) d.get(BasicSnippetData.Key.TARGET_BLOCK);
        final StatementBlock sb =
                new BlockContractRule.ValidityProgramConstructor(labels, block,
                                                                 variables, services).construct();
        Statement s = new MethodFrame(null, context, sb);
        JavaBlock result = JavaBlock.createJavaBlock(new StatementBlock(s));

        return result;
    }
}
