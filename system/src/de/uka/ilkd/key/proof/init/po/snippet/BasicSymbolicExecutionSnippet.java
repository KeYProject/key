package de.uka.ilkd.key.proof.init.po.snippet;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import java.util.Iterator;

/**
 *
 * @author christoph
 */
class BasicSymbolicExecutionSnippet extends ReplaceAndRegisterMethod
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
        posts = posts.append(d.tb.equals(poVars.exceptionAtPost,
                                         poVars.exception));
        posts = posts.append(d.tb.equals(poVars.heapAtPost, poVars.heap));
        final Term prog = buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
        return prog;
    }

    private Term buildProgramTerm(BasicSnippetData d,
                                  ProofObligationVars vs,
                                  Term postTerm,
                                  TermBuilder.Serviced tb) {
        if (d.getContractContent(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "precondition for a contract without precondition.");
        }
        assert Modality.class.equals(BasicSnippetData.Key.MODALITY.getType());
        Modality modality = (Modality) d.getContractContent(
                BasicSnippetData.Key.MODALITY);


        //create formal parameters
        ImmutableList<LocationVariable> formalParamVars =
                ImmutableSLList.<LocationVariable>nil();
        for (Term param : vs.localIns) {
            ProgramVariable paramVar = param.op(ProgramVariable.class);
            ProgramElementName pen = new ProgramElementName("_"
                    + paramVar.name());
            LocationVariable formalParamVar =
                    new LocationVariable(pen, paramVar.getKeYJavaType());
            formalParamVars = formalParamVars.append(formalParamVar);
            register(formalParamVar, tb.getServices());
        }

        //create java block
        final JavaBlock jb = buildJavaBlock(d, formalParamVars,
                                            vs.self != null
                                            ? vs.self.op(ProgramVariable.class)
                                            : null,
                                            vs.result != null
                                            ? vs.result.op(ProgramVariable.class)
                                            : null,
                                            vs.exception != null
                                            ? vs.exception.op(
                ProgramVariable.class)
                                            : null);

        //create program term
        final Modality symbExecMod;
        if (modality == Modality.BOX) {
            symbExecMod = Modality.DIA;
        } else if (modality == Modality.DIA) {
            symbExecMod = Modality.BOX;
        } else if (modality == Modality.BOX_TRANSACTION) {
            symbExecMod = Modality.DIA_TRANSACTION;
        } else {
            symbExecMod = Modality.BOX_TRANSACTION;
        }
        final Term programTerm = tb.prog(symbExecMod, jb, postTerm);

        //create update
        Term update = tb.skip();
        Iterator<LocationVariable> formalParamIt = formalParamVars.iterator();
        Iterator<Term> paramIt = vs.localIns.iterator();
        while (formalParamIt.hasNext()) {
            Term paramUpdate = tb.elementary(formalParamIt.next(),
                                             paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }

        return tb.apply(update, programTerm);
    }

    private JavaBlock buildJavaBlock(
            BasicSnippetData d,
            ImmutableList<LocationVariable> formalParVars,
            ProgramVariable selfVar,
            ProgramVariable resultVar,
            ProgramVariable exceptionVar) {
        if (!(d.targetMethod instanceof IProgramMethod)) {
            throw new UnsupportedOperationException("Tried to produce a "
                    + "java-block for an observer which is no progam method.");
        }
        JavaInfo javaInfo = d.tb.getServices().getJavaInfo();
        IProgramMethod pm = (IProgramMethod) d.targetMethod;

        //create method call
        final ImmutableArray<Expression> formalArray =
                new ImmutableArray<Expression>(formalParVars.toArray(
                new ProgramVariable[formalParVars.size()]));
        final StatementBlock sb;
        if (pm.isConstructor()) {
            assert selfVar != null;
            assert resultVar == null;
            final Expression[] formalArray2 =
                    formalArray.toArray(new Expression[formalArray.size()]);
            final New n =
                    new New(formalArray2, new TypeRef(d.forClass),
                            null);
            final CopyAssignment ca = new CopyAssignment(selfVar, n);
            sb = new StatementBlock(ca);
        } else {
            final MethodBodyStatement call =
                    new MethodBodyStatement(pm, selfVar, resultVar, formalArray);
            sb = new StatementBlock(call);
        }

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
