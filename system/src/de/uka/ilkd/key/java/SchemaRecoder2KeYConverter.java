// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java;

import java.util.List;

import recoder.list.generic.ASTList;
import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.recoderext.ProgramVariableSVWrapper;
import de.uka.ilkd.key.java.recoderext.TypeSVWrapper;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SchemaTypeReference;
import de.uka.ilkd.key.java.reference.SchematicFieldReference;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.IForUpdates;
import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.java.statement.ILoopInit;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramSV;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.metaconstruct.ArrayLength;
import de.uka.ilkd.key.rule.metaconstruct.ArrayPostDecl;
import de.uka.ilkd.key.rule.metaconstruct.ConstructorCall;
import de.uka.ilkd.key.rule.metaconstruct.CreateObject;
import de.uka.ilkd.key.rule.metaconstruct.DoBreak;
import de.uka.ilkd.key.rule.metaconstruct.EnhancedForElimination;
import de.uka.ilkd.key.rule.metaconstruct.EvaluateArgs;
import de.uka.ilkd.key.rule.metaconstruct.ExpandMethodBody;
import de.uka.ilkd.key.rule.metaconstruct.ForToWhile;
import de.uka.ilkd.key.rule.metaconstruct.InitArrayCreation;
import de.uka.ilkd.key.rule.metaconstruct.IsStatic;
import de.uka.ilkd.key.rule.metaconstruct.MethodCall;
import de.uka.ilkd.key.rule.metaconstruct.MultipleVarDecl;
import de.uka.ilkd.key.rule.metaconstruct.PostWork;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.rule.metaconstruct.SpecialConstructorCall;
import de.uka.ilkd.key.rule.metaconstruct.StaticInitialisation;
import de.uka.ilkd.key.rule.metaconstruct.SwitchToIf;
import de.uka.ilkd.key.rule.metaconstruct.TypeOf;
import de.uka.ilkd.key.rule.metaconstruct.Unpack;
import de.uka.ilkd.key.rule.metaconstruct.UnwindLoop;
import de.uka.ilkd.key.util.ExtList;

/**
 * This is an extension of the usual {@link Recoder2KeYConverter} that supports
 * schema variables.
 * 
 * Some entities have to be treated differently, but most conversions are
 * handled identically (via the superclass).
 * 
 * @author MU
 * 
 */
public class SchemaRecoder2KeYConverter extends Recoder2KeYConverter {

    /**
     * the type that is used for schema variables types.
     */
    public static KeYJavaType typeSVType 
    	= new KeYJavaType(PrimitiveType.PROGRAM_SV, ProgramSVSort.TYPE);

    /**
     * create a new schema-recoder-to-key converter. It must be associated with
     * a schema recoder2key.
     * 
     * @param rec2key
     *            the object to associate to
     * @param namespaceSet
     *            namespaces to resolve entity names
     * @param services
     *            services to be used
     */
    public SchemaRecoder2KeYConverter(SchemaRecoder2KeY rec2key, Services services, NamespaceSet namespaceSet) {
        super(rec2key, services, namespaceSet);
    }

    // ------ conversion methods

    /**
     * convert a program meta construct creating a new object corresponding to
     * the name.
     * 
     * If you add a ProgramTransformer to the system you will most propably
     * have to register it here.
     */
    public ProgramTransformer convert(
            de.uka.ilkd.key.java.recoderext.RKeYMetaConstruct mc) {

        ExtList list = new ExtList();
        String mcName = mc.getName();
        list.add(callConvert(mc.getChild()));
        if ("#switch-to-if".equals(mcName)) {
            return new SwitchToIf(list
                    .get(SchemaVariable.class));
        } else if ("#unwind-loop".equals(mcName)) {
            final ProgramSV[] labels = mc.getSV();
            return new UnwindLoop(labels[0], labels[1], list
                    .get(LoopStatement.class));
        } else if ("#unpack".equals(mcName)) {
            return new Unpack(list.get(For.class));
        } else if ("#for-to-while".equals(mcName)) {
            final ProgramSV[] labels = mc.getSV();
            return new ForToWhile(labels[0], labels[1], 
                    list.get(Statement.class));      
        }  else if ("#enhancedfor-elim".equals(mcName)){ 
            EnhancedFor efor = list.get(EnhancedFor.class);
            if(efor == null)
                throw new ConvertException("#enhancedfor-elim requires an enhanced for loop as argument");
            return new EnhancedForElimination(list.get(EnhancedFor.class));
        } else if ("#do-break".equals(mcName)) {
            return new DoBreak(list
                    .get(LabeledStatement.class));
        } else if ("#expand-method-body".equals(mcName)) {
            return new ExpandMethodBody(list
                    .get(SchemaVariable.class));
        } else if ("#method-call".equals(mcName)) {
            ProgramSV[] svw = mc.getSV();
            ProgramSV execSV = null;
            ProgramSV returnSV = null;
            for (int i = 0; i < svw.length; i++) {
                if (svw[i].sort() == ProgramSVSort.VARIABLE) {
                    returnSV = svw[i];
                }
                if (svw[i].sort() == ProgramSVSort.EXECUTIONCONTEXT) {
                    execSV = svw[i];
                }
            }
            return new MethodCall(execSV, returnSV, list
        	    .get(Expression.class));
        } else if ("#evaluate-arguments".equals(mcName)) {
            return new EvaluateArgs(list.get(Expression.class));
        } else if ("#constructor-call".equals(mcName)) {
            return new ConstructorCall(mc.getFirstSV().getSV(),
                    list.get(Expression.class));
        } else if ("#special-constructor-call".equals(mcName)) {
            return new SpecialConstructorCall(list
                    .get(Expression.class));
        } else if ("#post-work".equals(mcName)) {
            return new PostWork(list.get(SchemaVariable.class));
        } else if ("#static-initialisation".equals(mcName)) {
            return new StaticInitialisation(list
                    .get(Expression.class));
        } else if ("#resolve-multiple-var-decl".equals(mcName)) {
            return new MultipleVarDecl(list
                    .get(SchemaVariable.class));
        } else if ("#array-post-declaration".equals(mcName)) {
            return new ArrayPostDecl(list
                    .get(SchemaVariable.class));
        } else if ("#init-array-creation".equals(mcName)) {
            return new InitArrayCreation(mc.getFirstSV().getSV(),
                    list.get(Expression.class));
        } else {
            throw new ConvertException("Program meta construct "
                    + mc.toString() + " unknown.");
        }
    }

    /**
     * translate schema variables to ProgramMetaConstructs.
     * 
     * If you have an expression meta construct you will have to add it here.
     */
    public ProgramTransformer convert(
            de.uka.ilkd.key.java.recoderext.RKeYMetaConstructExpression mc) {
        ExtList list = new ExtList();
        String mcName = mc.getName();
        list.add(callConvert(mc.getChild()));
        if ("#create-object".equals(mcName)) {
            return new CreateObject(list.get(Expression.class));
        } else if ("#isstatic".equals(mc.getName())) {
            return new IsStatic(list.get(Expression.class));
        } else if ("#length-reference".equals(mcName)) {
            return new ArrayLength(list.get(Expression.class));
        } else {
            throw new ConvertException("Program meta construct "
                    + mc.toString() + " unknown.");
        }
    }

    /**
     * translate schema variables to ProgramMetaConstructs.
     * 
     * If you have a type meta construct you will have to add it here.
     */
    public ProgramTransformer convert(
            de.uka.ilkd.key.java.recoderext.RKeYMetaConstructType mc) {
        ExtList list = new ExtList();
        list.add(callConvert(mc.getChild()));
        if ("#typeof".equals(mc.getName0())) {
            return new TypeOf(list.get(Expression.class));
        } else {
            throw new ConvertException("Program meta construct "
                    + mc.toString() + " unknown.");
        }
    }

    /**
     * method-call-statements are expanded to method-frames
     */
    public MethodFrame convert(de.uka.ilkd.key.java.recoderext.RMethodCallStatement l) {
        ProgramVariableSVWrapper svw = l.getVariableSV();
        return new MethodFrame((IProgramVariable) (svw != null ? svw.getSV()
                : null), (IExecutionContext) callConvert(l
                        .getExecutionContext()), (StatementBlock) callConvert(l
                                .getBody()));
    }

    /**
     * translate method body statements.
     */
    public MethodBodyStatement convert(
            de.uka.ilkd.key.java.recoderext.RMethodBodyStatement l) {
        final IProgramVariable resVar = l.getResultVar() == null ? null
                : (IProgramVariable)l.getResultVar().getSV();

        final TypeReference tr;
        if (l.getBodySource() instanceof TypeSVWrapper) {
            tr = (TypeReference) ((TypeSVWrapper) l.getBodySource()).getSV();
        } else {
            tr = convert(l.getBodySource());
        }

        return new MethodBodyStatement(tr, resVar, convert(l
                .getMethodReference()));
    }

    /**
     * translate Context statement blocks
     */
    public ContextStatementBlock convert(
            de.uka.ilkd.key.java.recoderext.ContextStatementBlock csb) {
        ExtList children = collectChildren(csb);
        return new ContextStatementBlock(children,
                csb.getExecutionContext() == null ? null
                        : (IExecutionContext) callConvert(csb
                                .getExecutionContext()));
    }

    /**
     * translate exection contexts
     */
    public ExecutionContext convert(
            de.uka.ilkd.key.java.recoderext.ExecutionContext ec) {
        return new ExecutionContext((TypeReference) callConvert(ec.getTypeReference()), 
                                    (IProgramMethod) callConvert(ec.getMethodContext()),
				                        ec.getRuntimeInstance()!=null? (ReferencePrefix)callConvert(ec.getRuntimeInstance()) : null);
    }

    // ----- Schema Variables
    // SchemaVariables are unwrapped from their wrapping entity.

    public SchemaVariable convert(
            de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper svw) {

        return svw.getSV();
    }

    public SchemaVariable convert(
            de.uka.ilkd.key.java.recoderext.StatementSVWrapper svw) {
        return svw.getSV();
    }

    public SchemaVariable convert(
            de.uka.ilkd.key.java.recoderext.LabelSVWrapper svw) {
        return svw.getSV();
    }
    
    public SchemaVariable convert(
          de.uka.ilkd.key.java.recoderext.MethodSignatureSVWrapper svw) {
      return svw.getSV();
  }

    public SchemaVariable convert(
            de.uka.ilkd.key.java.recoderext.TypeSVWrapper svw) {
        return svw.getSV();
    }

    public SchemaVariable convert(
            de.uka.ilkd.key.java.recoderext.ExecCtxtSVWrapper svw) {
        return svw.getSV();
    }

    public SchemaVariable convert(
            de.uka.ilkd.key.java.recoderext.CatchSVWrapper svw) {
        return svw.getSV();
    }

    public SchemaVariable convert(
            de.uka.ilkd.key.java.recoderext.ProgramVariableSVWrapper svw) {

        return svw.getSV();
    }

    /**
     * for some reason the this and super references have to be treated
     * differently here.
     */

    public ThisReference convert(recoder.java.reference.ThisReference tr) {
        return new ThisReference();
    }

    public SuperReference convert(recoder.java.reference.SuperReference sr) {
        return new SuperReference();
    }

    /**
     * local variable declarations have to be treated differently if they have
     * schema vars in them.
     */
    public LocalVariableDeclaration convert(
            recoder.java.declaration.LocalVariableDeclaration lvd) {
        if (lvd.getTypeReference() instanceof TypeSVWrapper) {
            List<recoder.java.declaration.VariableSpecification> rspecs = lvd.getVariables();
            VariableSpecification[] varspecs = new VariableSpecification[rspecs
                                                                         .size()];
            for (int i = 0; i < rspecs.size(); i++) {
                varspecs[i] = convertVarSpecWithSVType(rspecs
                        .get(i));
            }
            SchemaVariable typesv = ((TypeSVWrapper) lvd.getTypeReference())
            .getSV();

            List<recoder.java.declaration.Modifier> mods = lvd.getModifiers();
            Modifier[] modifiers = new Modifier[mods == null ? 0 : mods.size()];
            for (int i = 0; i < modifiers.length; i++) {
                modifiers[i] = (Modifier) callConvert(mods.get(i));
            }

            return new LocalVariableDeclaration(modifiers, (ProgramSV) typesv,
                    varspecs);
        } else {
            // otherwise use the default case
            return super.convert(lvd);
        }
    }

    /*
     * helper to convert(LocalVariableDeclaration)
     */
    protected VariableSpecification convertVarSpecWithSVType(
            recoder.java.declaration.VariableSpecification recoderVarspec) {
        VariableSpecification varspec = (VariableSpecification) getMapping()
        .toKeY(recoderVarspec);
        if (varspec == null) {
            ExtList l = collectChildren(recoderVarspec);
            ProgramElement pv 
               = ProgramSVSort.VARIABLE.getSVWithSort(l, 
            					      ProgramElementName.class);
            if (pv instanceof ProgramElementName) { // sth. like #type i;
                KeYJavaType kjt = new KeYJavaType(typeSVType);
                pv = new LocationVariable((ProgramElementName) pv, kjt);
            }
            ProgramElement init = ProgramSVSort.VARIABLEINIT.getSVWithSort(l,
                    Expression.class);
            varspec = new VariableSpecification((IProgramVariable) pv,
                    recoderVarspec.getDimensions(), (Expression) init,
                    typeSVType, null);
            insertToMap(recoderVarspec, varspec);
        }
        return varspec;
    }

    /**
     * convert a recoder TypeReference to a KeY TypeReference (checks dimension
     * and hands it over)
     */
    public TypeReference convert(recoder.java.reference.TypeReference tr) {
        recoder.java.reference.ReferencePrefix rp = tr.getReferencePrefix();

        recoder.java.reference.PackageReference prefix = null;
        recoder.java.reference.PackageReference result = null;
        while (rp != null) {
            if (prefix == null) {
                result = new recoder.java.reference.PackageReference(
                        ((recoder.java.reference.UncollatedReferenceQualifier) rp)
                        .getIdentifier());
                prefix = result;
            } else {
                recoder.java.reference.PackageReference prefix2 = new recoder.java.reference.PackageReference(
                        ((recoder.java.reference.UncollatedReferenceQualifier) rp)
                        .getIdentifier());
                prefix.setReferencePrefix(prefix2);
                prefix = prefix2;
            }

            if (rp instanceof recoder.java.reference.ReferenceSuffix) {
                rp = ((recoder.java.reference.ReferenceSuffix) rp)
                .getReferencePrefix();
            } else {
                rp = null;
            }
        }

        // there is no explicit PackageReference convert method
        // but the cast is safe.
        PackageReference packref = result != null ? (PackageReference) convert(result)
                : null;

        return new SchemaTypeReference(new ProgramElementName(tr.getName()), tr
                .getDimensions(), packref);
    }

    /**
     * convert a recoder VariableSpecification to a KeY VariableSpecification
     * (checks dimension and hands it over and insert in hashmap)
     */
    public VariableSpecification convert(
            recoder.java.declaration.VariableSpecification recoderVarspec) {
        if (!(recoderVarspec.getIdentifier() instanceof ProgramVariableSVWrapper)) {
            return super.convert(recoderVarspec);
        }
        VariableSpecification varSpec = (VariableSpecification) getMapping()
        .toKeY(recoderVarspec);
        if (varSpec == null) {

            ExtList children = collectChildren(recoderVarspec);
            IProgramVariable progvar = (IProgramVariable) children
            .get(SchemaVariable.class);

            children.remove(progvar);
            varSpec = new VariableSpecification(children, progvar,
                    recoderVarspec.getDimensions(), null);
            insertToMap(recoderVarspec, varSpec);

        }
        return varSpec;
    }

    public Expression convert(recoder.java.reference.FieldReference fr) {
        ReferencePrefix prefix = null;
        if (fr.getReferencePrefix() != null) {
            prefix = (ReferencePrefix) callConvert(fr.getReferencePrefix());
        }
        SchemaVariable suffix = (SchemaVariable) callConvert(fr.getIdentifier());

        return new SchematicFieldReference(suffix, prefix);
    }

    public MethodReference convert(recoder.java.reference.MethodReference mr) {
        // convert reference prefix
        final ReferencePrefix prefix;
        if (mr.getReferencePrefix() instanceof recoder.java.reference.UncollatedReferenceQualifier) {
            // type references would be allowed
            final recoder.java.reference.UncollatedReferenceQualifier uncoll = (recoder.java.reference.UncollatedReferenceQualifier) mr
            .getReferencePrefix();
            prefix = convert(new recoder.java.reference.TypeReference(uncoll
                    .getReferencePrefix(), uncoll.getIdentifier()));
        } else {
            if (mr.getReferencePrefix() != null) {
                prefix = (ReferencePrefix) callConvert(mr.getReferencePrefix());
            } else {
                prefix = null;
            }
        }
        // convert MethodName
        MethodName name = (MethodName) callConvert(mr.getIdentifier());

        // convert arguments
        ASTList<recoder.java.Expression> recoderArgs = mr.getArguments();
        final Expression[] keyArgs;
        if (recoderArgs != null) {
            keyArgs = new Expression[recoderArgs.size()];
        } else {
            keyArgs = new Expression[0];
        }
        for (int i = 0, sz = keyArgs.length; i < sz; i++) {
            keyArgs[i] = (Expression) callConvert(recoderArgs.get(i));
        }

        return new MethodReference(new ImmutableArray<Expression>(keyArgs), name, prefix);
    }

    /**
     * converts a For.
     * 
     * @param f
     *            the For of recoder
     * @return the For of KeY
     */
    public For convert(recoder.java.statement.For f) {
        ILoopInit li;
        IForUpdates ifu;
        IGuard iGuard;
        if (f.getInitializers() != null
                && f.getInitializers().get(0) instanceof de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper) {
            de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper esvw = (de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper) f
            .getInitializers().get(0); // brrrr!
            li = (ProgramSV) esvw.getSV();
        } else {
            li = convertLoopInitializers(f);
        }

        if (f.getGuard() instanceof de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper) {
            de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper esvw = (de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper) f
            .getGuard();
            iGuard = (ProgramSV) esvw.getSV();
        } else {
            iGuard = convertGuard(f);
        }

        if (f.getUpdates() != null
                && f.getUpdates().get(0) instanceof de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper) {
            de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper esvw = (de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper) f
            .getUpdates().get(0);
            ifu = (ProgramSV) esvw.getSV();
        } else {
            ifu = convertUpdates(f);
        }

        return new For(li, iGuard, ifu, convertBody(f));
    }

}
