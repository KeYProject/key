package de.uka.ilkd.key.proof.init.po.snippet;

import java.util.Iterator;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.IForUpdates;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.init.ProofObligationVars;
import de.uka.ilkd.key.speclang.LoopInvariant;
import de.uka.ilkd.key.util.ExtList;

public class BasicLoopExecutionSnippet extends ReplaceAndRegisterMethod
        implements FactoryMethod {

    @Override
    public Term produce(BasicSnippetData d, ProofObligationVars poVars)
            throws UnsupportedOperationException {
        ImmutableList<Term> posts = ImmutableSLList.<Term>nil();
        if (poVars.selfAtPost != null)
            posts = posts.append(d.tb.equals(poVars.selfAtPost, poVars.self));
        
        if (poVars.guard != null)
            posts = posts.append(d.tb.equals(poVars.guardAtPost, poVars.guard));
        
        posts = posts.append(d.tb.equals(poVars.heapAtPost, d.tb.getBaseHeap()));
        
        final Term prog = buildProgramTerm(d, poVars, d.tb.and(posts), d.tb);
        return prog;
    }


    private Term buildProgramTerm(BasicSnippetData d,
                                  ProofObligationVars vs,
                                  Term postTerm,
                                  TermBuilder.Serviced tb) {
        if (d.get(BasicSnippetData.Key.MODALITY) == null) {
            throw new UnsupportedOperationException("Tried to produce a " +
                                                    "program-term for a loop without modality.");
        }
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
        if (vs.guard != null) {
            ProgramVariable paramVar = vs.guard.op(ProgramVariable.class);
            ProgramElementName pen = new ProgramElementName("_"
                    + paramVar.name());
            LocationVariable formalParamVar =
                    new LocationVariable(pen, paramVar.getKeYJavaType());
            formalParamVars = formalParamVars.append(formalParamVar);
            register(formalParamVar, tb.getServices());
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
        
        //create update
        Term update = tb.skip();
        Iterator<LocationVariable> formalParamIt = formalParamVars.iterator();
        Iterator<Term> paramIt = vs.localIns.append(vs.guard).iterator();
        while (formalParamIt.hasNext()) {
            Term paramUpdate = tb.elementary(formalParamIt.next(),
                    paramIt.next());
            update = tb.parallel(update, paramUpdate);
        }

        return tb.apply(update, programTerm);
    }
    
    private JavaBlock buildJavaBlock(BasicSnippetData d) {
        LoopInvariant inv = (LoopInvariant) d.get(BasicSnippetData.Key.LOOP_INVARIANT);
        LoopStatement sb = inv.getLoop();
        ExecutionContext context =
                (ExecutionContext) d.get(BasicSnippetData.Key.CONTEXT);

        Expression e = sb.getGuardExpression();
        Guard g = (Guard) sb.getGuard();
        Statement b = sb.getBody();
        LoopInit i = (LoopInit) sb.getILoopInit();
        IForUpdates u = sb.getIForUpdates();
        
        //create loop call
        if (sb instanceof Do) {
            sb = new Do(e, b, null);
        } else if (sb instanceof EnhancedFor) {
            sb = new EnhancedFor(i, g, sb, new ExtList(), null);
        } else if (sb instanceof For) {
            sb = new For(i, g, u, sb);
        } else if (sb instanceof While) {
            sb = new While(e, sb);
        } else {
            throw new UnsupportedOperationException("Loop statement is not properly specified.");
        }
        
        //create java block
        Statement s = new MethodFrame(null, context, new StatementBlock (sb));
        JavaBlock result = JavaBlock.createJavaBlock(new StatementBlock(s));

        return result;        
    }
}