package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.JavaInfo;
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
        if (d.getContractContent(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException("Tried to produce a " +
                     "program-term for a contract without modality.");
        }

        //create java block
        Modality modality =
                (Modality) d.getContractContent(BasicSnippetData.Key.MODALITY);
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
        JavaInfo javaInfo = d.tb.getServices().getJavaInfo();
        ProgramVariable exceptionVar = (ProgramVariable)d.origVars.exception.op();

        //create method call
        // TODO: handle break, continue, return...
        final StatementBlock sb = d.targetBlock;
//             new BlockContractRule.ValidityProgramConstructor(labels, d.targetBlock, variables, services).construct();

        //create variables for try statement
        final KeYJavaType eType =
                javaInfo.getTypeByClassName("java.lang.Exception");
        final TypeReference excTypeRef = javaInfo.createTypeReference(eType);
        final ProgramElementName ePEN = new ProgramElementName("e");
        final ProgramVariable eVar = new LocationVariable(ePEN, eType);

        //create try statement
        final CopyAssignment nullStat =
                new CopyAssignment(exceptionVar, NullLiteral.NULL);
        final VariableSpecification eSpec = new VariableSpecification(eVar);
        final ParameterDeclaration excDecl =
                new ParameterDeclaration(new Modifier[0], excTypeRef, eSpec,
                                         false);
        final CopyAssignment assignStat =
                new CopyAssignment(exceptionVar, eVar);
        final Catch catchStat =
                new Catch(excDecl, new StatementBlock(assignStat));
        final Try tryStat = new Try(sb, new Branch[]{catchStat});
        final StatementBlock sb2 = new StatementBlock(
                new Statement[]{nullStat, tryStat});

        //create java block
        JavaBlock result = JavaBlock.createJavaBlock(sb2);

        return result;
    }

}
