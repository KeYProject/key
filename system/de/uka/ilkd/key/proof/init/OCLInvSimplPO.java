// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/** @author Daniel Larsson */

package de.uka.ilkd.key.proof.init;

import java.io.*;
import java.util.Iterator;

import javax.swing.JFrame;
import javax.swing.JOptionPane;

import tudresden.ocl.check.types.Basic;
import tudresden.ocl.check.types.Type;
import de.uka.ilkd.key.casetool.*;
import de.uka.ilkd.key.casetool.together.UMLOCLTogetherModel;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.RigidFunction;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.logic.op.oclop.OclOp;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.oclsort.OclSort;
import de.uka.ilkd.key.parser.DefaultTermParser;
import de.uka.ilkd.key.parser.SimpleTermParser;
import de.uka.ilkd.key.pp.AbbrevMap;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.RuleSource;

/** 
 * Used for OCL Simplification.
 * Consists of two separate parts (and should probably be divided  
 * into two classes):
 * <ol> 
 *  <li> One part is responsible for adding the needed sorts and functions
 *       to the namespaces (InitConfig) used by the prover.
 *  </li>
 *  <li> The other part creates, given a model representation of
 *       a class, a proof obligation of its invariant in the form 
 *       of a term.
 *       The first step is to translate the OCL syntax to a representation
 *       expressed in the taclet language. This is done using the external
 *       program "ocl2taclet". The next step is then to apply the taclet
 *       parser to this representation, and the result is a Term 
 *       representation of the invariant. This term becomes a proof 
 *       obligation and can be handled by the prover.
 * </li>
 * </ol>
 */
public class OCLInvSimplPO extends OCLProofOblInput 
    implements OCLSimplificationPO {

    /** The "ocl2taclet" command */
    private static final String OCL2TACLET_COMMAND = "ocl2taclet";

    /** The name of the key file containing the OCL simplification rules */
    private static final String RULE_SOURCE = "oclSimplificationRules.key";

    protected ModelClass aClass;

    /** The proof obligation */
    private Term proofObl;

    public OCLInvSimplPO(ModelClass aClass) {
	super("Simplifying invariant of " + aClass.getClassName());
	this.aClass = aClass;
    }

    public Includes readIncludes() throws ProofInputException{
	RuleSource standard = RuleSource.initRuleFile(RULE_SOURCE);
	Includes includes = new Includes();
	includes.put("oclSimplificationRules", standard);
	return includes;
    }

    protected void setProofObligation(Term po) {
	proofObl = po;
    }


    public ModelClass getModelClass() {
	return aClass;
    }

    public ProofAggregate getPO() {
	if (proofObl == null) throw 
           new IllegalStateException("No proofObl term");
        String s = getProofHeader(aClass.getRootDirectory());
	return ProofAggregate.createProofAggregate(
           new Proof(name(), proofObl, s, 
		     initConfig.createTacletIndex(),
		     initConfig.createBuiltInRuleIndex(),
                     initConfig.getServices()), name());
    }

    /**
     * Creates and sets the proof obligation term.
     */
    public void readProblem(ModStrategy mod) {
        setProofObligation(generateInvSimplPO());
    }

    /**
     * Extracts the String invariant from the class representation
     * and rewrites it into a format accepted by the "ocl2taclet"
     * parser program.
     */
    protected String prepareInv(ModelClass aClass) {
	StringBuffer str = new StringBuffer(aClass.getMyInv());
	String pack = aClass.getContainingPackage();
	if (pack == null) {
	    pack = "NOPACKAGE";
	}
	String className = aClass.getClassName();
	str.insert(0, "package " + pack + "\ncontext " 
		   + className + " inv:\n  ");
	str.append("\nendpackage");
	return str.toString();
    }

    /**
     * Extracts the String invariant of the class representation,
     * turns it into a corresponding Term, and wraps it in some
     * other operators so that it can be handled by the prover.
     * @return Resulting Term.
     */
    protected Term generateInvSimplPO() {
	String preparedInv = prepareInv(aClass);
	String tacletInv = ordinaryOcl2tacletOcl(preparedInv, aClass.getRootDirectory());
	
	addNumeralLiterals(getInitConfig());
	NamespaceSet nss = getInitConfig().namespaces();

	//Parse the taclified OCL constraint into a Term
	Reader inReader = new StringReader(tacletInv);
        SimpleTermParser parser = new DefaultTermParser();
	Term term = null;
	try {
	    term = parser.parse(inReader, OclSort.OCLANY, getInitConfig().getServices(), 
				nss, new AbbrevMap());
	} catch (Exception ee) { 
	    ee.printStackTrace();
	} 

	//Wrap the resulting term in a predicate called "OclWrapper" 
	TermFactory tf = new TermFactory(); 
	TermSymbol oclWrapper 
	    = (Function)nss.functions().lookup(new Name("$OclWrapper"));

	/*
	TermSymbol insertSet 
	    = (TermSymbol)nss.functions().lookup(new Name("$insert_set"));
	TermSymbol emptySet 
	    = (TermSymbol)nss.functions().lookup(new Name("$empty_set"));
	*/
	TermSymbol consInv 
	    = (TermSymbol)nss.functions().lookup(new Name("$cons_inv"));
	TermSymbol nilInv 
	    = (TermSymbol)nss.functions().lookup(new Name("$nil_inv"));
	TermSymbol invariant 
	    = (Function)nss.functions().lookup(new Name("$invariant"));
	String className = aClass.getFullClassName();
	String uniqueClassName = className.replace('.', '~');
	TermSymbol classOp 
	    = (Function)nss.functions().lookup(new Name(uniqueClassName));
	Term classTerm = tf.createFunctionTerm(classOp);
	//Term emptySetTerm = tf.createFunctionTerm(emptySet);
	Term emptySetTerm = tf.createFunctionTerm(nilInv);
	Term invariantTerm 
	    = tf.createFunctionTerm(invariant, new Term[]{classTerm, term});
	/*
	Term setOfInvariantTerm 
	    = tf.createFunctionTerm(insertSet, new Term[]{invariantTerm, 
							  emptySetTerm});
	*/
	Term setOfInvariantTerm 
	    = tf.createFunctionTerm(consInv, new Term[]{invariantTerm, 
							emptySetTerm});
	
	//Term formula = tf.createFunctionTerm(oclWrapper, term);
	Term formula = tf.createFunctionTerm(oclWrapper, setOfInvariantTerm);
	return formula;
    } 

    /**
     * Applies the binary "ocl2taclet" to the String invariant.
     * @param preparedInv String invariant.
     * @param rootDir Directory where the file with model information,
     * "modelinfo.umltypes", is stored (needed by "ocl2taclet").
     * @return Invariant expressed in the taclet language.
     */
    private String ordinaryOcl2tacletOcl(String preparedInv, String rootDir) {
	//Invokes the "ocl2taclet" parser
	Process p = null;
	try {
	    //Runs "ocl2taclet modelinfo.umltypes"
	    p = Runtime.getRuntime().exec(new String[]{OCL2TACLET_COMMAND,
						       rootDir + "/modelinfo.umltypes"});

	    //Writes the invariant on the sub process' output stream
	    OutputStream out = p.getOutputStream();
	    OutputStreamWriter writer = new OutputStreamWriter(out);
	    writer.write(preparedInv);
	    writer.flush();
	    writer.close();
	} catch(IOException e1) {	    
	    JOptionPane.showMessageDialog
		(new JFrame(), "\"ocl2taclet\" execution failed:\n\n"+
		 e1+"\n\n"+
		 "To make use of ocl2taclet make sure that\n\n"+
		 "1. the directory where the binary resides is in "+
		 "your $PATH variable\n"+
		 "2. the binary has executable file permissions.",
		 "Error", 
		 JOptionPane.ERROR_MESSAGE);
            throw new RuntimeException("\"ocl2taclet\" execution failed.\n"+
                                       "Is the binary in your $PATH?");
	}

	//Wait for the sub process to terminate
	try {
	    p.waitFor();
	}
	catch(InterruptedException ie) {
	    ie.printStackTrace();
	}

	//Reads the input stream (the parse result) into a String
	InputStream in = p.getInputStream();
	StringBuffer buffer = new StringBuffer();
	try {
	    int ch = 0;
	    while ((ch = in.read()) != -1) {
		buffer.append((char)ch);
	    }
	} catch (IOException ioe) {
	    ioe.printStackTrace();
	}
	String result = new String(buffer);
	result = result.trim();

	//If result is empty there is a syntax error in constraint
	if (result.equals("")) {
	    JOptionPane.showMessageDialog
		(new JFrame(), "\"ocl2taclet\" execution failed:\n\n"+
		 "\n\n"+
		 "Syntax error in OCL constraint:\n\n" +
		 preparedInv,
		 "Error", 
		 JOptionPane.ERROR_MESSAGE);
            throw new RuntimeException("\"ocl2taclet\" execution failed");
	}
	return result;
    }

    /**
     * Adds OCL types, OCL operations, and model properties to the
     * name spaces of the initial configuration.
     * Can as well be hard-coded, since they are needed for all
     * OCL simplification. Also avoids trouble with taclet parser.
     * @param initConf The initial configuration whose set of name
     * spaces needs to be updated.
     */
    public void createNamespaceSet(InitConfig initConf) {
	addPredefinedOCLSorts(initConf);
	addPredefinedOCLOperations(initConf);
	addModelProperties(initConf);
	//addNumeralLiterals(initConf);
    }

    private static void addPredefinedOCLSorts(InitConfig initConf) {
	initConf.sortNS().add(OclSort.OCLINVARIANT);
	initConf.sortNS().add(OclSort.SET_OF_OCLINVARIANT);

	initConf.sortNS().add(OclSort.OCLGENERIC);
	initConf.sortNS().add(OclSort.OCLANY);
	initConf.sortNS().add(OclSort.OCLTYPE);
	initConf.sortNS().add(OclSort.REAL);
	initConf.sortNS().add(OclSort.INTEGER);
	initConf.sortNS().add(OclSort.STRING);
	initConf.sortNS().add(OclSort.BOOLEAN);
	initConf.sortNS().add(OclSort.CLASSIFIER);

	initConf.sortNS().add(OclSort.COLLECTION_OF_OCLGENERIC);
	initConf.sortNS().add(OclSort.COLLECTION_OF_OCLANY);
	initConf.sortNS().add(OclSort.COLLECTION_OF_OCLTYPE);
	initConf.sortNS().add(OclSort.COLLECTION_OF_REAL);
	initConf.sortNS().add(OclSort.COLLECTION_OF_INTEGER);
	initConf.sortNS().add(OclSort.COLLECTION_OF_STRING);
	initConf.sortNS().add(OclSort.COLLECTION_OF_BOOLEAN);
	initConf.sortNS().add(OclSort.COLLECTION_OF_CLASSIFIER);

	initConf.sortNS().add(OclSort.SET_OF_OCLGENERIC);
	initConf.sortNS().add(OclSort.SET_OF_OCLANY);
	initConf.sortNS().add(OclSort.SET_OF_OCLTYPE);
	initConf.sortNS().add(OclSort.SET_OF_REAL);
	initConf.sortNS().add(OclSort.SET_OF_INTEGER);
	initConf.sortNS().add(OclSort.SET_OF_STRING);
	initConf.sortNS().add(OclSort.SET_OF_BOOLEAN);
	initConf.sortNS().add(OclSort.SET_OF_CLASSIFIER);

	initConf.sortNS().add(OclSort.BAG_OF_OCLGENERIC);
	initConf.sortNS().add(OclSort.BAG_OF_OCLANY);
	initConf.sortNS().add(OclSort.BAG_OF_OCLTYPE);
	initConf.sortNS().add(OclSort.BAG_OF_REAL);
	initConf.sortNS().add(OclSort.BAG_OF_INTEGER);
	initConf.sortNS().add(OclSort.BAG_OF_STRING);
	initConf.sortNS().add(OclSort.BAG_OF_BOOLEAN);
	initConf.sortNS().add(OclSort.BAG_OF_CLASSIFIER);

	initConf.sortNS().add(OclSort.SEQUENCE_OF_OCLGENERIC);
	initConf.sortNS().add(OclSort.SEQUENCE_OF_OCLANY);
	initConf.sortNS().add(OclSort.SEQUENCE_OF_OCLTYPE);
	initConf.sortNS().add(OclSort.SEQUENCE_OF_REAL);
	initConf.sortNS().add(OclSort.SEQUENCE_OF_INTEGER);
	initConf.sortNS().add(OclSort.SEQUENCE_OF_STRING);
	initConf.sortNS().add(OclSort.SEQUENCE_OF_BOOLEAN);
	initConf.sortNS().add(OclSort.SEQUENCE_OF_CLASSIFIER);
    }

    private static void addPredefinedOCLOperations(InitConfig initConf) {
	initConf.funcNS().add(OclOp.INVARIANT);
	initConf.funcNS().add(OclOp.CONS_INV);
	initConf.funcNS().add(OclOp.NIL_INV);

	initConf.funcNS().add(new RigidFunction(new Name("OclAny"), 
						  OclSort.OCLTYPE, 
						  new Sort[0]));
	initConf.funcNS().add(new RigidFunction(new Name("OclType"), 
						  OclSort.OCLTYPE, 
						  new Sort[0]));
	initConf.funcNS().add(new RigidFunction(new Name("OclBoolean"), 
						  OclSort.OCLTYPE, 
						  new Sort[0]));
	initConf.funcNS().add(new RigidFunction(new Name("OclReal"), 
						  OclSort.OCLTYPE, 
						  new Sort[0]));
	initConf.funcNS().add(new RigidFunction(new Name("OclInteger"), 
						  OclSort.OCLTYPE, 
						  new Sort[0]));
	initConf.funcNS().add(new RigidFunction(new Name("OclString"), 
						  OclSort.OCLTYPE, 
						  new Sort[0]));
	initConf.funcNS().add(new RigidFunction(new Name("OclClassifier"), 
						  OclSort.OCLTYPE, 
						  new Sort[0]));

	initConf.funcNS().add(OclOp.ITERATE);
	initConf.funcNS().add(OclOp.FOR_ALL);
	initConf.funcNS().add(OclOp.EXISTS);
	initConf.funcNS().add(OclOp.IF);
	initConf.funcNS().add(OclOp.ALL_SUBTYPES);
	initConf.funcNS().add(OclOp.ALL_INSTANCES);
	initConf.funcNS().add(OclOp.INSERT_SET);
	initConf.funcNS().add(OclOp.INSERT_BAG);
	initConf.funcNS().add(OclOp.INSERT_SEQUENCE);
	initConf.funcNS().add(OclOp.EMPTY_SET);
	initConf.funcNS().add(OclOp.EMPTY_BAG);
	initConf.funcNS().add(OclOp.EMPTY_SEQUENCE);
	initConf.funcNS().add(OclOp.UNION);
	initConf.funcNS().add(OclOp.INTERSECTION);
	initConf.funcNS().add(OclOp.DIFFERENCE);
	initConf.funcNS().add(OclOp.SYMMETRIC_DIFFERENCE);
	initConf.funcNS().add(OclOp.SELECT);
	initConf.funcNS().add(OclOp.REJECT);
	initConf.funcNS().add(OclOp.COLLECT);
	initConf.funcNS().add(OclOp.TRUE);
	initConf.funcNS().add(OclOp.FALSE);
	initConf.funcNS().add(OclOp.AND);
	initConf.funcNS().add(OclOp.EQUALS);
	initConf.funcNS().add(OclOp.OCL_WRAPPER);
	initConf.funcNS().add(OclOp.SELF);
	initConf.funcNS().add(OclOp.SIZE);
	initConf.funcNS().add(OclOp.INCLUDES);
	initConf.funcNS().add(OclOp.EXCLUDES);
	initConf.funcNS().add(OclOp.COUNT);
	initConf.funcNS().add(OclOp.INCLUDES_ALL);
	initConf.funcNS().add(OclOp.EXCLUDES_ALL);
	initConf.funcNS().add(OclOp.IS_EMPTY);
	initConf.funcNS().add(OclOp.NOT_EMPTY);
	initConf.funcNS().add(OclOp.SUM);
	initConf.funcNS().add(OclOp.IS_UNIQUE);
	initConf.funcNS().add(OclOp.SORTED_BY);
	initConf.funcNS().add(OclOp.ANY);
	initConf.funcNS().add(OclOp.ONE);
	initConf.funcNS().add(OclOp.INCLUDING);
	initConf.funcNS().add(OclOp.EXCLUDING);
	initConf.funcNS().add(OclOp.AS_SET);
	initConf.funcNS().add(OclOp.AS_BAG);
	initConf.funcNS().add(OclOp.AS_SEQUENCE);
	initConf.funcNS().add(OclOp.APPEND);
	initConf.funcNS().add(OclOp.PREPEND);
	initConf.funcNS().add(OclOp.SUB_SEQUENCE);
	initConf.funcNS().add(OclOp.AT);
	initConf.funcNS().add(OclOp.FIRST);
	initConf.funcNS().add(OclOp.LAST);
	initConf.funcNS().add(OclOp.NOT_EQUALS);
	initConf.funcNS().add(OclOp.OCL_IS_NEW);
	initConf.funcNS().add(OclOp.OR);
	initConf.funcNS().add(OclOp.XOR);
	initConf.funcNS().add(OclOp.NOT);
	initConf.funcNS().add(OclOp.IMPLIES);
	initConf.funcNS().add(OclOp.LESS_THAN);
	initConf.funcNS().add(OclOp.LESS_THAN_EQ);
	initConf.funcNS().add(OclOp.GREATER_THAN);
	initConf.funcNS().add(OclOp.GREATER_THAN_EQ);
	initConf.funcNS().add(OclOp.PLUS);
	initConf.funcNS().add(OclOp.MINUS);
	initConf.funcNS().add(OclOp.TIMES);
	initConf.funcNS().add(OclOp.DIV_INFIX);
	initConf.funcNS().add(OclOp.DIV);
	initConf.funcNS().add(OclOp.MOD);
	initConf.funcNS().add(OclOp.MIN);
	initConf.funcNS().add(OclOp.MAX);
	initConf.funcNS().add(OclOp.MINUS_PREFIX);
	initConf.funcNS().add(OclOp.ABS);


	/*
	IteratorOfNamed it = initConf.sortNS().allElements().iterator();
	while (it.hasNext()) {
	    Sort sort = (Sort)it.next();
	    if (sort instanceof ClassInstanceSortImpl) {
		initConf.sortNS().add(new OclObject(sort.name()));
	    }
	}
	*/
    }

    /**
     * Uses ".../casetool/together/UMLOCLTogetherModel" together with
     * the classes in ".../casetool/" to extract classifiers, attributes,
     * (query) methods, and associations and add them to the function
     * namespace.
     */
    private static void addModelProperties(InitConfig initConf){
	//Add all classifiers and properties from the UML model
	//to the namespace
	UMLOCLTogetherModel umlModel = new UMLOCLTogetherModel(null);
	Iterator iter = umlModel.getUMLOCLClassifiers().values().iterator();
	while (iter.hasNext()) {
	    UMLOCLClassifier classifier = (UMLOCLClassifier)iter.next();
	    String cName = classifier.getFullName();
	    String uniqueClassName = cName.replace('.', '~');
	    Name className = new Name(uniqueClassName);
	    initConf.funcNS().add(new NonRigidFunction(className, OclSort.OCLTYPE, 
	    				      new Sort[0]));
	    Iterator featureIter = classifier.features().values().iterator();
	    while (featureIter.hasNext()) {
		UMLOCLFeature feature = (UMLOCLFeature)featureIter.next();
		String fName = feature.getName();
		Type type = feature.getType();
		Sort featureSort = null;
		if (type instanceof Basic) {
		    if (type == Basic.BOOLEAN) {
			featureSort = OclSort.BOOLEAN;
		    } else if (type == Basic.INTEGER) {
			featureSort = OclSort.INTEGER;
		    } else if (type == Basic.REAL) {
			featureSort = OclSort.REAL;
		    } else if (type == Basic.STRING) {
			featureSort = OclSort.STRING;
		    }
		} else if (type instanceof tudresden.ocl.check.types.OclType) {
		    featureSort = OclSort.OCLTYPE;
		} else if (type instanceof tudresden.ocl.check.types.Collection) {
		    /*
		    Type elementType = type.getElementType();
		    if (type.getCollectionKind() == tudresden.ocl.check.types.Collection.SET) {
			if (elementType instanceof Basic) {
			    if (elementType == Basic.BOOLEAN) {
				featureSort = OclSort.SET_OF_BOOLEAN;
			    } else if (elementType == Basic.INTEGER) {
				featureSort = OclSort.SET_OF_INTEGER;
			    } else if (elementType == Basic.REAL) {
				featureSort = OclSort.SET_OF_REAL;
			    } else if (elementType == Basic.STRING) {
				featureSort = OclSort.SET_OF_STRING;
			    }
			} else if (elementType instanceof tudresden.ocl.check.types.OclType) {
			    featureSort = OclSort.SET_OF_OCLTYPE;
			}
		    } else if (type.getCollectionKind() == tudresden.ocl.check.types.Collection.BAG) {
		        if (elementType instanceof Basic) {
			    if (elementType == Basic.BOOLEAN) {
				featureSort = OclSort.BAG_OF_BOOLEAN;
			    } else if (elementType == Basic.INTEGER) {
				featureSort = OclSort.BAG_OF_INTEGER;
			    } else if (elementType == Basic.REAL) {
				featureSort = OclSort.BAG_OF_REAL;
			    } else if (elementType == Basic.STRING) {
				featureSort = OclSort.BAG_OF_STRING;
			    }
			} else if (elementType instanceof tudresden.ocl.check.types.OclType) {
			    featureSort = OclSort.BAG_OF_OCLTYPE;
			}
		    } else {
		        if (elementType instanceof Basic) {
			    if (elementType == Basic.BOOLEAN) {
				featureSort = OclSort.SEQUENCE_OF_BOOLEAN;
			    } else if (elementType == Basic.INTEGER) {
				featureSort = OclSort.SEQUENCE_OF_INTEGER;
			    } else if (elementType == Basic.REAL) {
				featureSort = OclSort.SEQUENCE_OF_REAL;
			    } else if (elementType == Basic.STRING) {
				featureSort = OclSort.SEQUENCE_OF_STRING;
			    }
			} else if (elementType instanceof tudresden.ocl.check.types.OclType) {
			    featureSort = OclSort.SEQUENCE_OF_OCLTYPE;
			}
		    }
		    */
		    featureSort = OclSort.COLLECTION_OF_OCLANY;
		} else {
		    featureSort = OclSort.CLASSIFIER;
		}
		String uniqueFeatureName = uniqueClassName + "~" +
		    fName.replace(',', '+')
		    .replace('.', '~');
		int leftParIndex = uniqueFeatureName.indexOf("(");
		if (leftParIndex > -1) {
		    int rightParIndex = uniqueFeatureName.indexOf(")");
		    StringBuffer buffer = new StringBuffer(uniqueFeatureName);
		    buffer = buffer.replace(leftParIndex, leftParIndex+1, "+~");
		    buffer = buffer.replace(rightParIndex, rightParIndex+1, "~+");
		    uniqueFeatureName = buffer.toString();
		}
		Name featureName = new Name(uniqueFeatureName);
		if (feature instanceof UMLOCLStructuralFeature) {
		    initConf.funcNS().add(new NonRigidFunction(featureName, featureSort, 
		    					      new Sort[]{OclSort.CLASSIFIER}));
		} else {
		    int numOfArgs = ((UMLOCLBehaviouralFeature)feature).getParameters().length + 1;
		    Sort[] argSorts = new Sort[numOfArgs];
		    argSorts[0] = OclSort.CLASSIFIER;
		    for (int i=1; i<numOfArgs; i++) {
			argSorts[i] = OclSort.OCLANY;
		    }
		    initConf.funcNS().add(new NonRigidFunction(featureName, featureSort, 
		    					      argSorts));
		}
	    }
	    Iterator assocIter = classifier.getAssociations().values().iterator();
	    while (assocIter.hasNext()) {
		UMLOCLAssociation assoc = (UMLOCLAssociation)assocIter.next();
		String aName = assoc.getTargetRole();
		String uniqueAssocName = uniqueClassName + "~" + aName;
		Name assocName = new Name(uniqueAssocName);
		initConf.funcNS().add(new NonRigidFunction(assocName, OclSort.COLLECTION_OF_CLASSIFIER, 
							  new Sort[]{OclSort.CLASSIFIER}));
	    }
	}
    }

    /**
     * Adds the integer operations to the function namespace
     * of the initial configuration. Gives them the proper Sort.
     */
    private static void addNumeralLiterals(InitConfig initConf) {
	//Add numeral literals to the namespace
	//(must have type/sort OclSort.INTEGER)
	initConf.funcNS().add(new RigidFunction(new Name("#"), 
						  OclSort.INTEGER, 
						  new Sort[0]));
	initConf.funcNS().add(new RigidFunction(new Name("Z"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("0"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("1"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("2"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("3"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("4"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("5"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("6"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("7"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("8"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
	initConf.funcNS().add(new RigidFunction(new Name("9"), 
						  OclSort.INTEGER, 
						  new Sort[]{OclSort.INTEGER}));
    }

    public static void createNamespaceSetForTests(InitConfig initConf) {
	addPredefinedOCLSorts(initConf);
	addPredefinedOCLOperations(initConf);
	addNumeralLiterals(initConf);
    }
}
