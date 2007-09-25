// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java;

import java.io.IOException;
import java.io.StringReader;
import java.util.HashMap;
import java.util.List;

import recoder.java.declaration.TypeDeclaration;
import recoder.list.generic.ASTArrayList;
import recoder.list.generic.ASTList;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.recoderext.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.metaconstruct.*;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.ExtList;
import de.uka.ilkd.key.util.KeYRecoderExcHandler;

public class SchemaRecoder2KeY extends Recoder2KeY implements SchemaJavaReader{
    
    /** the namespace containing the program schema variables allowed here*/
    protected Namespace svns;

    public static KeYJavaType typeSVType = new KeYJavaType(PrimitiveType.PROGRAM_SV, ProgramSVSort.TYPE);

    /** caches access to methods for reflection */
    private final static HashMap schemaCt2meth = new HashMap(400);

    /** caches constructor access for reflection */
    private final static HashMap recClass2schemakeyClassCons = new HashMap(400);

    // could this be the servConf of the super class?
    private static SchemaCrossReferenceServiceConfiguration schemaServConf = 
	new SchemaCrossReferenceServiceConfiguration(new KeYRecoderExcHandler());

    public SchemaRecoder2KeY(Services services,
			     NamespaceSet nss) {
	super(services, nss);
    }



    /**
     * returns the hashmap of a concrete RecodeR class to the constructor of its 
     * corresponding KeY class. Speeds up reflection.
     * Attention must be overwritten by subclasses!
     */
    protected HashMap getKeYClassConstructorCache() {
	return recClass2schemakeyClassCons;
    }

    protected HashMap getMethodCache() {
	return schemaCt2meth;
    }

    public void setSVNamespace(Namespace svns) {
	this.svns = svns;
    }

    /** creates an empty RECODER compilation unit 
     * @return the recoder.java.CompilationUnit 
     */
    public Context createEmptyContext() {
	return new Context
	    (schemaServConf, new recoder.java.CompilationUnit(),
	     schemaServConf.getProgramFactory().createClassDeclaration
	     (null, new ImplicitIdentifier("<KeYSpecialParsing>"), 
	      null, null, null));
    }

    public ProgramMetaConstruct 
	convert(de.uka.ilkd.key.java.recoderext.RKeYMetaConstruct mc) {

	ExtList list = new ExtList();
	String mcName = mc.getName();
	list.add(callConvert(mc.getChild()));
	if ("#switch-to-if".equals(mcName)){
	    return new SwitchToIf((SchemaVariable)list.get(SchemaVariable.class));
	} else if ("#unwind-loop".equals(mcName)) {
            final ProgramSV[] labels = mc.getSV();
            return new UnwindLoop
		(labels[0], labels[1], 
                        (LoopStatement)list.get(LoopStatement.class));	 
	} else if ("#unpack".equals(mcName)) {	
	    return new Unpack((For)list.get(For.class));
	} else if ("#do-break".equals(mcName)) {	
	    return new DoBreak((LabeledStatement)list.get(LabeledStatement.class));
	} else if ("#expand-method-body".equals(mcName)) {		    
	    return new ExpandMethodBody((SchemaVariable)list.
					get(SchemaVariable.class));
	} else if ("#method-call".equals(mcName) || 
                   "#method-call-contract".equals(mcName)) {
	    ProgramSV[] svw    = mc.getSV();
	    ProgramSV execSV   = null;
	    ProgramSV returnSV = null;
	    for (int i=0; i<svw.length; i++) {
		if (svw[i].sort()==ProgramSVSort.VARIABLE) {
		    returnSV = svw[i];
		}
		if (svw[i].sort()==ProgramSVSort.EXECUTIONCONTEXT) {
		    execSV = svw[i];
		}		
	    }
            if ("#method-call".equals(mcName)) {
                return new MethodCall(execSV, returnSV,
				  (Expression)list.get(Expression.class));
            } else {
                return new MethodCallContract(execSV, returnSV,
                          (Expression)list.get(Expression.class));
            }
	} else if ("#evaluate-arguments".equals(mcName)) {
	    return new EvaluateArgs((Expression)list.get(Expression.class)); 
	} else if ("#constructor-call".equals(mcName)) {	
	    return new ConstructorCall
		(mc.getFirstSV().getSV(), 
		 (Expression)list.get(Expression.class));
	} else if ("#special-constructor-call".equals(mcName)) {	
	    return new SpecialConstructorCall
		((Expression)list.get(Expression.class));
	} else if ("#post-work".equals(mcName)) {	
	    return new PostWork
		((SchemaVariable)list.get(SchemaVariable.class));
	} else if ("#static-initialisation".equals(mcName)) {	
	    return new StaticInitialisation
		((Expression)list.get(Expression.class));
	} else if ("#resolve-multiple-var-decl".equals(mcName)) {	
	    return new MultipleVarDecl
		((SchemaVariable)list.get(SchemaVariable.class));
	} else if ("#array-post-declaration".equals(mcName)) {	
	    return new ArrayPostDecl
		((SchemaVariable)list.get(SchemaVariable.class));
	} else if ("#init-array-creation".equals(mcName)) {	
	    return new InitArrayCreation
		    (mc.getFirstSV().getSV(), 
		     (Expression)list.get(Expression.class));
	} else if ("#init-array-creation-transient".equals(mcName)) {	
	    return new InitArrayCreation
		    (mc.getFirstSV().getSV(), 
		     (Expression)list.get(Expression.class), true);
	} else if ("#enhancedfor-elim".equals(mcName)){ 
            EnhancedFor efor = (EnhancedFor)list.get(EnhancedFor.class);
            if(efor == null)
                throw new ConvertException("#enhancedfor-elim requires an enhanced for loop as argument");
            return new EnhancedForElimination((EnhancedFor)list.get(EnhancedFor.class));
        } else{	
	    throw new ConvertException("Program meta construct "
				       +mc.toString()
				       +" unknown.");	
	}
    }
 	

    public ProgramMetaConstruct 
	convert(de.uka.ilkd.key.java.recoderext.RKeYMetaConstructExpression mc) {
	ExtList list=new ExtList();
	String mcName = mc.getName();
	list.add(callConvert(mc.getChild()));
	if ("#create-object".equals(mcName)) {
	    return new CreateObject((Expression)list.get(Expression.class));
	} else if ("#isstatic".equals(mc.getName())) {
	    return new IsStatic((Expression)list.get(Expression.class));	    
	} else if ("#length-reference".equals(mcName)) {
	    return new ArrayLength((Expression)list.get(Expression.class));
	} else {
	    throw new ConvertException("Program meta construct "
				       + mc.toString()
				       + " unknown.");	
	}
    }


    public ProgramMetaConstruct 
	convert(de.uka.ilkd.key.java.recoderext.RKeYMetaConstructType mc) {
	ExtList list = new ExtList();
	list.add(callConvert(mc.getChild()));
	if ("#typeof".equals(mc.getName0())) {
	    return new TypeOf
		((Expression)list.get(Expression.class));
	} else {
	    throw new ConvertException("Program meta construct "
				       +mc.toString()
				       +" unknown.");	
	}
    }

    public MethodFrame 
	convert(de.uka.ilkd.key.java.recoderext.RMethodCallStatement l) {
	ProgramVariableSVWrapper svw = l.getVariableSV();
	return new MethodFrame
	    ((IProgramVariable) (svw != null ? svw.getSV() : null), 
	     (IExecutionContext) callConvert(l.getExecutionContext()),
	     (StatementBlock)callConvert(l.getBody()));
    }
 
    public MethodBodyStatement 
        convert(de.uka.ilkd.key.java.recoderext.RMethodBodyStatement l) { 
        final IProgramVariable resVar = (IProgramVariable) 
        ( l.getResultVar() == null ? null : l.getResultVar().getSV());
                
	final TypeReference tr;
	if (l.getBodySource() instanceof TypeSVWrapper) {
	    tr = (TypeReference)((TypeSVWrapper)l.getBodySource()).getSV();
	} else {
	    tr = convert(l.getBodySource());
	}
	               
        return new MethodBodyStatement(tr, resVar, convert(l.getMethodReference()));
    }

    public ContextStatementBlock
	convert(de.uka.ilkd.key.java.recoderext.ContextStatementBlock csb) {
	ExtList children = collectChildren(csb);
	return new ContextStatementBlock(
                               children, csb.getExecutionContext() == null ? 
			       null : 
			       (IExecutionContext)
			       callConvert(csb.getExecutionContext()));
    }


    public SchemaVariable
	convert(de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper svw) {

	return svw.getSV();
    }


    public SchemaVariable
	convert(de.uka.ilkd.key.java.recoderext.StatementSVWrapper svw) {

	return svw.getSV();
    }

    public ThisReference convert
	(recoder.java.reference.ThisReference tr) {
	return new ThisReference();
    }

    public SuperReference convert
	(recoder.java.reference.SuperReference sr) {
	return new SuperReference();
    }

    public SchemaVariable
	convert(de.uka.ilkd.key.java.recoderext.LabelSVWrapper svw) {

	return svw.getSV();
    }


    public SchemaVariable
	convert(de.uka.ilkd.key.java.recoderext.TypeSVWrapper svw) {

	return svw.getSV();
    }

    public SchemaVariable
	convert(de.uka.ilkd.key.java.recoderext.ExecCtxtSVWrapper svw) {
	return svw.getSV();
    }

    public ExecutionContext
	convert(de.uka.ilkd.key.java.recoderext.ExecutionContext ec) {
	return new ExecutionContext
	    ((TypeReference)callConvert(ec.getTypeReference()), 
	     (ReferencePrefix)callConvert(ec.getRuntimeInstance()));
    }

    public SchemaVariable
	convert(de.uka.ilkd.key.java.recoderext.CatchSVWrapper svw) {
	return svw.getSV();
    }

    public SchemaVariable
	convert(de.uka.ilkd.key.java.recoderext.ProgramVariableSVWrapper svw) {

	return svw.getSV();
    }
    
    /**
     * wraps a RECODER ClassDeclaration in a compilation unit
     * @param classDecl the recoder.java.ClassDeclaration to wrap
     * @param cUnit the recoder.java.CompilationUnit where the class is wrapped
     * @return the enclosing recoder.java.CompilationUnit
     */
    protected recoder.java.CompilationUnit embedClass
	(recoder.java.declaration.ClassDeclaration classDecl,
	 Context context) { 
	
	recoder.java.CompilationUnit cUnit = 
	    context.getCompilationUnitContext();

	// add class to compilation unit
	ASTList<TypeDeclaration> typeDecls = 	    
	    cUnit.getDeclarations();

	if (typeDecls==null) {
	    typeDecls=new ASTArrayList<TypeDeclaration>(0); 
	} else {
	    typeDecls = (ASTList<TypeDeclaration>) 
		typeDecls.deepClone();
	}
	typeDecls.add(classDecl);

 	recoder.java.CompilationUnit compUnitContext
 	    = (recoder.java.CompilationUnit)cUnit.deepClone();
	
	compUnitContext.setDeclarations(typeDecls);
	compUnitContext.makeParentRoleValid();
	schemaServConf.getChangeHistory().attached(compUnitContext);
	schemaServConf.getChangeHistory().updateModel();
	return compUnitContext;
    }  


    /** parses a given JavaBlock using the context to determine the right 
     * references and returns a statement block of recoder.
     * @param block a String describing a java block
     * @param context recoder.java.CompilationUnit in which the block has 
     * to be interpreted
     * @return the parsed and resolved recoder statement block
     */
    protected recoder.java.StatementBlock 
	recoderBlock(String block, Context context) { 
	recoder.java.StatementBlock bl = null;

	SchemaJavaProgramFactory factory
	    = (SchemaJavaProgramFactory) schemaServConf.getProgramFactory();
	factory.setSVNamespace(svns);
	try {
	    bl=factory.parseStatementBlock(new StringReader(block));
	} catch (recoder.ParserException e) {
	    Debug.out("readSchemaJavaBlock(Reader,CompilationUnit)"
		      + " caused the " +
		      "exception:\n", e);
	    Debug.printStackTrace(e);
	    throw new ConvertException
		("Parsing: \n **** BEGIN ****\n "+ block + 
		 "\n **** END ****\n failed. Thrown Exception:" +
		 e.toString());
	} catch (IOException ioe) {
	    Debug.out("readSchemaJavaBlock(Reader,CompilationUnit)"
		      + " caused the IO exception:\n", ioe);
	    Debug.printStackTrace(ioe);
	    throw new ConvertException
		("IO Error when parsing: \n **** BEGIN ****\n "+ block +
		 "\n **** END ****\n failed. Thrown IOException:" + 
		 ioe.toString());
	}	

	embedClass(embedMethod(embedBlock(bl), context), context);

	return bl;
    }


    /**
     * converts a For.
     * @param f the For of recoder
     * @return the For of KeY
     */
    public For convert(recoder.java.statement.For f) {

	ILoopInit li;
	IForUpdates ifu;
	IGuard iGuard;
	if (f.getInitializers()!=null && 
	    f.getInitializers().get(0) 
	    instanceof de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper) {
	    de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper esvw
		= (de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper)
		f.getInitializers().get(0); //brrrr!
	    li = (ProgramSV)esvw.getSV();
	} else {
	    li = convertLoopInitializers(f);
	}
	
	if (f.getGuard() instanceof 
	    de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper) {
	    de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper esvw
		= (de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper)
		f.getGuard();
	    iGuard = (ProgramSV)esvw.getSV();
	} else {
	    iGuard = convertGuard(f);
	}

       
	if (f.getUpdates() != null && f.getUpdates().get(0) 
	    instanceof de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper) {
	    de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper esvw
		= (de.uka.ilkd.key.java.recoderext.ExpressionSVWrapper)
		f.getUpdates().get(0);
	    ifu = (ProgramSV)esvw.getSV();
	} else {
	    ifu = convertUpdates(f);
	}

	return new For(li, iGuard, ifu, convertBody(f));
    }

     protected VariableSpecification convertVarSpecWithSVType
 	(recoder.java.declaration.VariableSpecification recoderVarspec){
	 VariableSpecification varspec=
 	    (VariableSpecification) rec2key().toKeY(recoderVarspec);
 	if (varspec==null) {	    
 	    ExtList l=collectChildren(recoderVarspec);	    
	    ProgramElement pv
		= ProgramSVSort.VARIABLE.getSVWithSort(l, 
						       ProgramElementName.class);
	    if (pv instanceof ProgramElementName) {  //sth. like #type i;
		KeYJavaType kjt=new KeYJavaType(typeSVType);
		pv=new LocationVariable((ProgramElementName)pv, kjt);
	    }
	    ProgramElement init
		= ProgramSVSort.VARIABLEINIT.getSVWithSort
		(l, Expression.class);
 	    varspec = new VariableSpecification((IProgramVariable)pv, 
						recoderVarspec.getDimensions(),
						(Expression)init,
						typeSVType, null);
 	    insertToMap(recoderVarspec, varspec);
 	}
 	return varspec;
     }

     public LocalVariableDeclaration
 	convert(recoder.java.declaration.LocalVariableDeclaration lvd) {  
 	if (lvd.getTypeReference() instanceof TypeSVWrapper) {
 	    List<recoder.java.declaration.VariableSpecification> rspecs = lvd.getVariables();
 	    VariableSpecification[] varspecs
 		= new VariableSpecification[rspecs.size()];
 	    for (int i=0; i<rspecs.size(); i++) {
 		varspecs[i] = convertVarSpecWithSVType
 		    (rspecs.get(i));
 	    }
 	    SchemaVariable typesv
 		= ((TypeSVWrapper)lvd.getTypeReference()).getSV();

	    List<recoder.java.declaration.Modifier> mods = lvd.getModifiers();
	    Modifier[] modifiers = new Modifier[mods==null? 0 : mods.size()];
	    for (int i = 0; i<modifiers.length; i++) {
		modifiers[i] = (Modifier) callConvert(mods.get(i));
	    }
	    
 	    return new LocalVariableDeclaration(modifiers, 
						(ProgramSV)typesv, 
						varspecs);
 	} else {
 	    return super.convert(lvd);
 	}
     }


     /** 
      * convert a recoder TypeReference to a KeY TypeReference
      * (checks dimension and hands it over)
      */
     public TypeReference 
 	convert(recoder.java.reference.TypeReference tr) {

	 recoder.java.reference.ReferencePrefix rp = tr.getReferencePrefix(); 

	 recoder.java.reference.PackageReference prefix = null;		 
	 recoder.java.reference.PackageReference result = null;		 
	 while (rp != null) {	     
	     if (prefix == null) {
		 result = new recoder.java.reference.PackageReference
		     (((recoder.java.reference.UncollatedReferenceQualifier)rp).getIdentifier());
		 prefix = result;
	     } else {
		 recoder.java.reference.PackageReference prefix2 = 
		     new recoder.java.reference.PackageReference
		     (((recoder.java.reference.UncollatedReferenceQualifier)rp).getIdentifier());
		 prefix.setReferencePrefix(prefix2);
		 prefix = prefix2;		 
	     }

	     if (rp instanceof recoder.java.reference.ReferenceSuffix) {
		 rp = ((recoder.java.reference.ReferenceSuffix)rp).getReferencePrefix();
	     } else {
		 rp = null;
	     }
	 }
 		 

	 return new SchemaTypeReference
	     (new ProgramElementName(tr.getName()), 
	      tr.getDimensions(), result != null ? 
	      convert(result) : null);
     }




     /** convert a recoder VariableSpecification to a KeY
      * VariableSpecification
      * (checks dimension and hands it over and insert in hashmap)
      */
     public VariableSpecification
 	convert(recoder.java.declaration.VariableSpecification recoderVarspec){	

 	if (! (recoderVarspec.getIdentifier() instanceof ProgramVariableSVWrapper)) {
 	    return super.convert(recoderVarspec);
 	}
 	VariableSpecification varSpec
 	    = (VariableSpecification)rec2key().toKeY(recoderVarspec);
 	if (varSpec==null) {
 	
 	    ExtList children = collectChildren(recoderVarspec);
 	    IProgramVariable progvar 
		= (IProgramVariable) children.get(SchemaVariable.class);

	    children.remove(progvar);
 	    varSpec = new VariableSpecification(children, 
 					    progvar,
 					    recoderVarspec.getDimensions(),
 					    null);
 	    insertToMap(recoderVarspec, varSpec);

 	}
 	return varSpec;
     }


    public Expression convert
	 (recoder.java.reference.FieldReference fr) {

	 ReferencePrefix prefix = null;	
	 if (fr.getReferencePrefix() != null) {
	     prefix = (ReferencePrefix)callConvert(fr.getReferencePrefix());
	 }

         SchemaVariable suffix = (SchemaVariable) callConvert(fr.getIdentifier());
         
         return new SchematicFieldReference(suffix, prefix);
    }

    public MethodReference convert
	 (recoder.java.reference.MethodReference mr) {

	 // convert reference prefix    
	final ReferencePrefix prefix;	
	if (mr.getReferencePrefix() instanceof recoder.java.reference.UncollatedReferenceQualifier) {
	    // type references would be allowed
	    final recoder.java.reference.UncollatedReferenceQualifier uncoll = 
		(recoder.java.reference.UncollatedReferenceQualifier) mr.getReferencePrefix();
	    prefix = convert(new recoder.java.reference.
			     TypeReference(uncoll.getReferencePrefix(), 
					   uncoll.getIdentifier()));
	} else {
	    if (mr.getReferencePrefix() != null) {
		prefix = (ReferencePrefix)callConvert(mr.getReferencePrefix());
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
	for (int i = 0, sz = keyArgs.length; i<sz; i++) {
	    keyArgs[i] = (Expression)callConvert(recoderArgs.get(i));
	}

	return new MethodReference(new ArrayOfExpression(keyArgs), name, prefix);
    }
    
    public void parseSpecialClasses() {
    }
} 
