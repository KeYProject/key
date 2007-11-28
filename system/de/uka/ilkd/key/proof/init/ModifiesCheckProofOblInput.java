// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.proof.init;

import java.util.*;

import recoder.io.PathList;
import recoder.io.ProjectSettings;

import de.uka.ilkd.key.casetool.ModelMethod;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.*;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.visitor.ProgramTypeCollector;
import de.uka.ilkd.key.jml.UsefulTools;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.proof.ModifiesParserHelper;
import de.uka.ilkd.key.proof.OpReplacer;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.RuleSource;
import de.uka.ilkd.key.proof.mgt.Contract;
import de.uka.ilkd.key.proof.mgt.Contractable;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.KeYExceptionHandler;


/** represents a proof obligation originating from a given Modifies Clause
 * as input for the prover.
 * @deprecated Replaced by RespectsModifiesPO.
 */
public class ModifiesCheckProofOblInput implements ProofOblInput {

    private ModelMethod methRepr;
    protected String name;

    protected InitConfig initConfig;
    
    protected Term proofObl;

    protected SetOfTerm modifiesElements;
    protected Set occuringClasses;
    protected Set currentClassAttributes;

    protected KeYExceptionHandler exceptionHandler;

    protected JavaInfo javaInfo;
    protected ProgramMethod m;
    protected String methodName;

    protected ProgramVariable self;
    //private ProgramVariable pv;
    protected Vector pvVector;

    protected HashMap location2descriptor = null;

    //private Vector parameterNames = new Vector();
    protected Vector parameterTypes;

//    private Namespace ns = new Namespace();

    private int resultNameCnt = 0;
    
    /** the term factory used to create terms */
    final TermFactory tf = TermFactory.DEFAULT;

    /** creates a new representation of a proof obligation from a Modifies 
     * Clause with the given name, originating from a representation of a model
     * method and having the given String as text of the Modifies Clause.
     * The given XMI file name can be used to read the underlying model.
     */
    public ModifiesCheckProofOblInput(String name, ModelMethod aMethRepr) {
	this.name=name+(aMethRepr != null ? " "+aMethRepr.getName() : "");
	this.methRepr=aMethRepr;
    }

    
    public String getJavaPath() {
        return methRepr.getContainingClass().getRootDirectory();
    }


    /** returns false, that is the input never asks the user which
     * environment he prefers
     */
    public boolean askUserForEnvironment() {
	return false;
    }
    
    public void setExceptionHandler(KeYExceptionHandler keh){
	exceptionHandler = keh;
    }

    /** generates the proof obligation
     *
     */
    public void readProblem(ModStrategy mod) {
	if (initConfig==null) {
	    throw new IllegalStateException("InitConfig not set.");
	}
        
	javaInfo = initConfig.getServices().getJavaInfo();
	
	getAllFromModParsHelper();
	
	// extracts the signature as a list
	ListOfType signatureList = createSignatureList();

	final KeYJavaType enclosingClassType = 
	    javaInfo.getKeYJavaType(methRepr.getContainingClass().getFullClassName());
	// finds the current program method
	m = javaInfo.getProgramMethod
	    (enclosingClassType, methodName, signatureList, enclosingClassType);
	//last argument added. hope it is right. /AR
	
	// puts all occuring classes into the set occuringClasses
	collectOccuringClasses(enclosingClassType);
	
	this.proofObl = createProof();
    }


    private void getAllFromModParsHelper(){
	ModifiesParserHelper modParserH = 
	    new ModifiesParserHelper(methRepr, initConfig.getServices(), initConfig.namespaces());
	
	// starts the internal computation of the helper class
	modParserH.parseModifiesClauseToHashSet(methRepr.getMyModifClause());
	
	modifiesElements = modParserH.getModifiesElements();
	methodName = modParserH.getMethodName();
	self = modParserH.getPVSelf();
	pvVector = modParserH.getPVVector();
	parameterTypes = modParserH.getParameterTypesVector();
    }

    private ListOfType createSignatureList(){
	ListOfType signatureList = SLListOfType.EMPTY_LIST;
	int index = parameterTypes.size()-1;
	while (index >= 0){
	    signatureList = signatureList.prepend((Type) parameterTypes.
	    				  elementAt(index));
	    index = index - 1;
	}
	return signatureList;
    }

    protected void collectOccuringClasses(KeYJavaType type) {
	ProgramTypeCollector mCollector = 
	    new ProgramTypeCollector(m, self, type, initConfig.getServices(),
				     new HashSet());
	mCollector.start();
	occuringClasses = mCollector.getResult();

	if (type!= null) {
	    occuringClasses.add(type);
	}

	// get the transitive closure of the occuring classes in the
	// sense that for each class the type of all its' attributes
	// is in the resulting Set

	Set occuringClassesToAdd = (HashSet) ((HashSet) occuringClasses).clone();
	KeYJavaType current = null;
	while (!(occuringClassesToAdd.isEmpty())){
	    current = (KeYJavaType) occuringClassesToAdd.iterator().next();
	    
	    Type currClassType = current.getJavaType();
	    KeYJavaType currentBase = current;
	    while (currClassType instanceof ArrayDeclaration) {
		currentBase = ((ArrayDeclaration) currClassType).
		    getBaseType().getKeYJavaType();
		currClassType = currentBase.getJavaType();
	    }
	    if (!(currClassType instanceof PrimitiveType || 
		  currClassType instanceof NullType)){
	    	// get all attributes of the given class
		ListOfField allAttributes = 
		    javaInfo.getKeYProgModelInfo().getAllFieldsLocallyDeclaredIn(currentBase);

		IteratorOfField iterateAttributes = allAttributes.iterator();
		
		
		while (iterateAttributes.hasNext()){
                    final ProgramVariable att = 
                        (ProgramVariable) 
                        iterateAttributes.next().getProgramVariable();
                                        
		    if (!att.isImplicit()){
                        final KeYJavaType addToOccCla = 
                            (KeYJavaType) att.getKeYJavaType();
			if (!(occuringClasses.contains(addToOccCla))){
			    occuringClasses.add(addToOccCla);
			    occuringClassesToAdd.add(addToOccCla);
			}
		    }
		}
	    }
	    occuringClassesToAdd.remove(current);
	}
    }
    
    
    protected Term createProof() {
	Term formula;
	if(self != null){
	    formula = tf.createJunctorTermAndSimplify
		(Op.IMP, tf.createJunctorTerm
		 (Op.NOT, tf.createEqualityTerm
		         (tf.createVariableTerm(self),
		                 tf.createFunctionTerm(Op.NULL))), 
		 createProofStart());
	}else{
	    formula = createProofStart();
	}
	return formula;
    }
    
    protected Term createProofStart() {
	Iterator iterateClasses = occuringClasses.iterator();
	Term accumulateClassFormulas = 
	    tf.createJunctorTerm(Op.TRUE);
	KeYJavaType currClass;
	while (iterateClasses.hasNext()) {
	    currClass = (KeYJavaType) iterateClasses.next();
	    if(javaInfo.getNullType()!=currClass){
	    accumulateClassFormulas = 
		tf.createJunctorTermAndSimplify
		(Op.AND, createClassFormula(currClass),
		 accumulateClassFormulas);
	    }
	}
	return tf.createJunctorTermAndSimplify
	    (Op.IMP, tf.createFunctionTerm(javaInfo.getInReachableState()),
	     accumulateClassFormulas);
    }
    
    private Term createClassFormula(KeYJavaType currClass){
	LogicVariable oprime  = new LogicVariable
	    (new Name("o"), 
	     currClass.getSort());
	
	// generate formula starting with \forall o': currClass
	Term classFormula = tf.createQuantifierTerm
	    (Op.ALL,
	     oprime ,
	     createClassSubFormula(currClass, oprime));


	return classFormula;
    }
    
    private Term createClassSubFormula(KeYJavaType currClass, 
				       LogicVariable oprime){
	Type currClassType = currClass.getJavaType();
	// stop primitive types from getting checked for attributes, there are
	// none anyway
	if (currClassType instanceof PrimitiveType)
	    {return tf.createJunctorTerm(Op.TRUE);}

	Term classSubFormula;
	
	ListOfField allAttributes;
	// get all attributes of the given class
	if (currClassType instanceof ClassDeclaration) {
	    allAttributes = javaInfo.getKeYProgModelInfo().getAllFieldsLocallyDeclaredIn
		(javaInfo.getKeYJavaType(currClassType));
	    IteratorOfField iterateAttributes = allAttributes.iterator();
	    
	    // initial value is TRUE which is the value of an empty conjunction
	    // as this formula is a conjunction this is the correct value in 
	    // case there are no elements
	    Term accumulateAttributeFormulas = 
		tf.createJunctorTerm(Op.TRUE);
	    
	    ProgramVariable currAttribute = null;
	    
	    while (iterateAttributes.hasNext()){
		currAttribute = (ProgramVariable) 
		    iterateAttributes.next().getProgramVariable();

		accumulateAttributeFormulas =
		    tf.createJunctorTermAndSimplify
		    (Op.AND, 
		     createAttributeFormula(currAttribute, currClass, oprime),
		     accumulateAttributeFormulas);
	    }

	    classSubFormula = accumulateAttributeFormulas;
	    
	}else {
	    // maybe check whether it is an ArrayDeclaration with test below:
	    // check it; may be artificial nulltype
	    if (currClassType instanceof ArrayDeclaration) {
		classSubFormula = createArrayFormula(currClass, oprime);
	    } else {
		// is this correct?
		classSubFormula = tf.createJunctorTerm(Op.TRUE);
	    }
	}

	Term nullTerm = tf.createFunctionTerm(Op.NULL);
	Term ov = tf.createVariableTerm(oprime);
	Term nn = tf.createJunctorTerm(
	    Op.NOT, tf.createEqualityTerm(ov, nullTerm));

        Term eqc = UsefulTools.isCreated(ov, initConfig.getServices());
	/*        ProgramVariable ci = 
	    initConfig.getServices().getJavaInfo().
	    getAttribute(ImplicitFieldAdder.IMPLICIT_CLASS_INITIALIZED, 
	            (ObjectSort) oprime.sort());
        
	Term eqi = tf.createEqualityTerm(
	    tf.createVariableTerm(ci), initConfig.getServices().
	    getTypeConverter().convertToLogicElement(BooleanLiteral.TRUE));
	    eqc = tf.createJunctorTermAndSimplify(Op.AND, eqc, eqi);*/
	classSubFormula = tf.createJunctorTermAndSimplify(
	    Op.IMP, tf.createJunctorTerm(Op.AND, nn, eqc), classSubFormula);
	return classSubFormula;
    }
    
    
    private Term createAttributeFormula(ProgramVariable currAttribute,
					KeYJavaType currClass,
					LogicVariable oprime) {	
        if (!currAttribute.isImplicit()){
            
            // create conjunction of o' != o111, o' != o112, ... for non-static
            // create "false" in case of a static attribute which is part of
            // the modifies clause and "true" if it not part of the m.c.
            
            // some initial value
            Term ante = tf.createJunctorTerm(Op.TRUE);
            
            IteratorOfTerm modifiesIterator = modifiesElements.iterator();
            TypeConverter typeConv =
                initConfig.getServices().getTypeConverter();
            final Term t_oprime = tf.createVariableTerm(oprime);
            
            while (modifiesIterator.hasNext()) {
		Term modTerm = modifiesIterator.next();
                
                if ( (!(modTerm.op() instanceof ProgramVariable) || 
		      ((ProgramVariable)modTerm.op()).isStatic()) &&
		     ! (modTerm.op() instanceof ArrayOp)){
                    ante = createModifiesFormulaForAttribute(currAttribute, 
                            currClass, ante, modTerm, typeConv, t_oprime);
                } else {
                    if (modTerm.op() instanceof ProgramVariable) {
                        // The modifies element has been a single ProgramVariable,
                        // meaning no dereferencing has happened. In this case there
                        // is nothing that can be done because this shouldn't happen
                        // Only attributes can be changed and thus only those are 
                        // relevant in the modifies clause.
                        // THROW EXCEPTION HERE !!!
                        System.out.println("Error - Element with no dereferencing "+
                                "in the modifies clause: " + modTerm);
                    }
                    if (modTerm.op() instanceof ArrayOp) {
                        // nothing to do here as an array element is not
                        // relevant for a normal attribute
                    }
                }	
            }
            
            // create part after the implication arrow
            LogicVariable x  = new LogicVariable
            (new Name("x"), 
                    currAttribute.getKeYJavaType().getSort());
            
            // Create the MethodReference belonging to the method whose modifies
            // clause is being checked here.
            Expression[] p = new Expression[pvVector.size()];
            for (int i = 0; i < pvVector.size(); i = i+1) {
                p[i] = (ProgramVariable) pvVector.elementAt(i);
            }
            
            StatementBlock mBlock = createMethodCall(p);
            
            
            final Term t_x = tf.createVariableTerm(x);
            final Term primedAttribute = 
                tf.createAttributeTerm(currAttribute, t_oprime);
            
            Term post = tf.createQuantifierTerm
            (Op.ALL, x, tf.createJunctorTermAndSimplify
                    (Op.IMP, tf.createEqualityTerm(t_x, primedAttribute),
                            tf.createBoxTerm
                            (JavaBlock.createJavaBlock(mBlock), 
                                    tf.createEqualityTerm
                                    (t_x, primedAttribute))));
            
            return tf.createJunctorTermAndSimplify(Op.IMP, ante, post);
        }
        else {
            return tf.createJunctorTerm(Op.TRUE);
        }
    }

    /**
     * @param currAttribute
     * @param currClass
     * @param ante
     * @param modProgVar
     * @param typeConv
     * @param t_oprime
     * @return
     */
    private Term createModifiesFormulaForAttribute
	(ProgramVariable currAttribute, KeYJavaType currClass, 
	 Term ante, Term modTerm, TypeConverter typeConv, final Term t_oprime){
        
        // static attribute
        if (modTerm.op() instanceof ProgramVariable) {
            // Check if the attributes match
            if (modTerm.op()==currAttribute){
                // build formula
                ante = tf.createJunctorTerm(Op.FALSE);
            }
        }else {
	    ProgramVariable modProgAttrib = (ProgramVariable) 
		((AttributeOp) modTerm.op()).attribute();
	    BasicLocationDescriptor bloc = (BasicLocationDescriptor)
		location2descriptor.get(modTerm);
	    modTerm = modTerm.sub(0);
	    
	    KeYJavaType classType = javaInfo.getKeYJavaType(modTerm.sort());
            // Check if the Class Types match
            if (classType == currClass) {
                // Check if the attributes match
                if (modProgAttrib == currAttribute){
		    Term anteSub = tf. createJunctorTerm(Op.NOT, 
							 tf.createEqualityTerm
							 (t_oprime, modTerm));
		    anteSub = tf.createJunctorTermAndSimplify(Op.IMP,
							      bloc.getFormula(),
							      anteSub);
		    // quantify free variables in the prefix
		    if(modTerm.freeVars().size() >0){
			anteSub = tf.createQuantifierTerm
			    (Op.ALL, new ArrayOfQuantifiableVariable
			     (modTerm.freeVars().toArray()), anteSub);
		    }
                    // build formula
                    ante = tf.createJunctorTermAndSimplify
			(Op.AND, anteSub, ante);
                }
            }
        }
        return ante;

    }
    

    private Term createArrayFormula(KeYJavaType currClass,
				    LogicVariable oprime) {
	// create conjunction of o' != o111, o' != o112, ... 
	// all this with a "check" before it for the right array index
	
	TypeConverter typeConv = 
	    initConfig.getServices().getTypeConverter();
	
	LogicVariable lambda  = new LogicVariable
	    (new Name("lambda"), 
	     typeConv.getIntegerLDT().targetSort()); 	
	
	// initial value true, as it is the value of an empty conjunction
	// and our terms are connected conjunctively	
        Term ante = 
	    tf.createJunctorTerm(Op.TRUE);
	
	IteratorOfTerm modifiesIterator = modifiesElements.iterator();
	while (modifiesIterator.hasNext()) {
	    Term modTerm = modifiesIterator.next();
	    //	    modElm = typeConv.convertToProgramElement(modTerm);
	    
	    //	    modProgVar = modElm;

	    //check whether it is appropriate to add this to the ante
	    //	    if (modProgVar instanceof ArrayReference){
	    if(modTerm.op() instanceof ArrayOp &&
	       javaInfo.getKeYJavaType(modTerm.sub(0).sort())==currClass){
		Term preCond = tf.createJunctorTerm(Op.TRUE);
		if(modTerm.sub(1).freeVars().size() == 0){
		    preCond = tf.createEqualityTerm
			(modTerm.sub(1), tf.createVariableTerm(lambda));
		}
		Debug.assertTrue(modTerm.sub(1).freeVars().size() <= 1);
		BasicLocationDescriptor bloc = (BasicLocationDescriptor)
		    location2descriptor.get(modTerm);
		HashMap replaceMap = new HashMap();
		replaceMap.put(modTerm.sub(1).freeVars().iterator().next(),
			       lambda);
		OpReplacer or = new OpReplacer(replaceMap);
		preCond = 
		    tf.createJunctorTermAndSimplify(Op.AND, preCond,
						    or.replace(bloc.getFormula()));
		// o' != o_ij
		Term postCond = tf.createJunctorTerm
		    (Op.NOT, tf.createEqualityTerm
		     (tf.createVariableTerm(oprime), modTerm.sub(0)));
		
		Term cond = 
		    tf.createJunctorTermAndSimplify(Op.IMP, preCond, postCond);
		
		// quantify free variables in the prefix
		if(modTerm.sub(0).freeVars().size() >0){
		    cond = tf.createQuantifierTerm
			(Op.ALL, new ArrayOfQuantifiableVariable
			 (modTerm.sub(0).freeVars().toArray()), cond);
		}

		// build parts together into the ante formula
		ante = tf.createJunctorTermAndSimplify(Op.AND, cond, ante); 
	    } else {
		// The modifies element has not been an ArrayReference,
		// that means it has nothing to do with the current class/array
		// as that is an array and we can thus ignore this element of
		// the modifies clause
	    }	
	}
	
	// create part after the outer implication arrow
	LogicVariable x  = new LogicVariable
	    (new Name("x"), 
	     ((ArrayDeclaration) currClass.getJavaType()).getBaseType().getKeYJavaType().getSort()
	     );
	
	// Create the MethodReference belonging to the method whose modifies
	// clause is being checked here.
	Expression[] p = new Expression[pvVector.size()];
	for (int i = 0; i < pvVector.size(); i = i+1) {
	    p[i] = (ProgramVariable) pvVector.elementAt(i);
	}
	
	StatementBlock mBlock = createMethodCall(p);
		
	Term equality = tf.createEqualityTerm
          (tf.createVariableTerm(x),
           tf.createArrayTerm 
           (ArrayOp.getArrayOp(oprime.sort()), 
                 tf.createVariableTerm(oprime),
           tf.createVariableTerm(lambda)) );
    
	Term post = tf.createQuantifierTerm
	    (Op.ALL, x,
	     tf.createJunctorTermAndSimplify
	     (Op.IMP, equality,  
	      tf.createBoxTerm
	      (JavaBlock.createJavaBlock(mBlock), equality)));

	
	Term arrayFormula = tf.
	    createJunctorTermAndSimplify(Op.IMP, ante, post);

	
	// helpers for the next block below
	final Function leq = typeConv.getIntegerLDT().getLessOrEquals();
	final Function lt  = typeConv.getIntegerLDT().getLessThan();
	final Term zero = 
	    typeConv.getIntegerLDT().translateLiteral(new IntLiteral(0));
	final Term validArrayTerm0 = tf.createFunctionTerm
	    (leq, zero, tf.createVariableTerm(lambda));
	final ProgramVariable lengthPV = (ProgramVariable) 
	    ((ArrayDeclaration) currClass.getJavaType()).length()
	    .getFieldSpecifications().getFieldSpecification(0)
	    .getProgramVariable();
	final Term lengthTerm = tf.createAttributeTerm
	    (lengthPV, tf.createVariableTerm(oprime));
	final Term validArrayTerm1 = tf.createFunctionTerm
	    (lt, tf.createVariableTerm(lambda), lengthTerm);

	// creates the 0<= lambda /\ lambda < o'.length() -> rest
	arrayFormula = tf.createJunctorTermAndSimplify
	    (Op.IMP, tf.createJunctorTermAndSimplify
	            (Op.AND, validArrayTerm0, validArrayTerm1), 
	            arrayFormula);
	
	// generate and return formula starting with \forall \lambda: int
	return tf.createQuantifierTerm(Op.ALL, lambda, arrayFormula);
    }

    private StatementBlock createMethodCall(Expression[] p){
	if(m.isConstructor()){
	    TypeRef prefix = new TypeRef(self.getKeYJavaType());
	    New n = new New(p,
			    prefix,
			    prefix);
	    return new StatementBlock(n);
	}else{
	    ProgramVariable result = null;
	    if(m.getKeYJavaType() != null){
		result =
		    new LocationVariable(new ProgramElementName(
					  "_result" + resultNameCnt++),
					m.getKeYJavaType());
		initConfig.namespaces().programVariables().add(result);
	    }
	    MethodBodyStatement mBS = new MethodBodyStatement
		(m,
		 self,
		 result,
		 new ArrayOfExpression(p));
	    return new StatementBlock(mBS);
	}
    }


    public ProofAggregate getPO() {
        if (proofObl == null) throw
           new IllegalStateException("No proofObl term");
        // now a static call since there is no suitable common superclass
        String s = OCLProofOblInput.createProofHeader(
            initConfig,
            methRepr.getContainingClass().getRootDirectory());
	return ProofAggregate.createProofAggregate(
	    new Proof(name(), proofObl, s,
		      initConfig.createTacletIndex(),
		      initConfig.createBuiltInRuleIndex(),
		      initConfig.getServices()),
	    name());
    }


    /** sets the initial configuration that is used to read the OCL
     * input and that is used to be modified during reading.
     */
    public void setInitConfig(InitConfig conf) {
	this.initConfig=conf;
        initConfig.sortNS().startProtocol();
        initConfig.funcNS().startProtocol();
        initConfig.progVarNS().startProtocol();
    }

    /** returns the name of the modifies check proof obligation input.
     */
    public String name() {
	return name;
    }

    public void readActivatedChoices() throws ProofInputException {
	
    }
    
    /** reads the include section and returns an Includes object.  
     */
    public Includes readIncludes() throws ProofInputException {
	RuleSource standard = RuleSource.initRuleFile("standardRules.key");
	Includes includes = new Includes();
	includes.put("standardRules", standard);
	return includes;
    }

    public void readSpecs(){
	// nothing here
    }

    public Term getPOTerm() {
	return proofObl;
    }
    
    
    public SetOfTerm getModifiesElements() {
	return modifiesElements;
    }

    public Contractable[] getObjectOfContract() {
        return new Contractable[]{methRepr};
    }

    public boolean initContract(Contract ct) {
        return false; //%%
    }

    public void startProtocol() {
	// do nothing
    }

    
}
