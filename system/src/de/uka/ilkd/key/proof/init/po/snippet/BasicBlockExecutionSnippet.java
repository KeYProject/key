package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Label;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.rule.BlockContractRule;
import de.uka.ilkd.key.speclang.BlockContract.Variables;
import java.util.ArrayList;


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
        final Term prog = buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
        return prog;
    }


    private Term buildProgramTerm(BasicSnippetData d,
                                  ProofObligationVars vs,
                                  Term postTerm,
                                  TermBuilder.Serviced tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException("Tried to produce a " +
                                                    "program-term for a contract without modality.");
        }

        //create java block
        Modality modality =
                (Modality) d.get(BasicSnippetData.Key.MODALITY);
        final JavaBlock jb = buildJavaBlock(d, vs);

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


    private JavaBlock buildJavaBlock(BasicSnippetData d,
                                     ProofObligationVars vs) {
        Services services = d.tb.getServices();

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
        JavaBlock result = JavaBlock.createJavaBlock(sb);

        return result;
    }
}
