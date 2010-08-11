// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
// Universitaet Koblenz-Landau, Germany
// Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.jmltest;

import java.io.*;
import java.util.Iterator;
import java.util.Vector;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.cspec.ComputeSpecification;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.PrettyPrinter;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.Public;
import de.uka.ilkd.key.java.declaration.modifier.Static;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.logic.ConstrainedFormula;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.proofobligation.SpecExtPO;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.QuanAssignmentPairLazy;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.OperationContract;
import de.uka.ilkd.key.speclang.OperationContractImpl;
import de.uka.ilkd.key.unittest.ppAndJavaASTExtension.CompilableJavaCardPP;
import de.uka.ilkd.key.util.ExtList;

/**
 * This class contains methods, that gather all needed information from current
 * proof and that are needed to create a wrapper-file
 * 
 * @author mbender@uni-koblenz.de
 */
public class WrapperConstructor extends Thread {

    private final JMLTestFileCreator jmltfc;

    private final SpecExtPO po;

    private final String className;

    private final Proof proof;

    private final JMLExport jmlEx;

    private final ProgramMethod pm;

    public WrapperConstructor(final JMLTestFileCreator jmltfc, final Proof proof) {
	this.jmltfc = jmltfc;
	this.proof = proof;
	po = (SpecExtPO) proof.getPO();
	pm = po.getProgramMethod();
	className = pm.getContainerType().getName();
	jmlEx = new JMLExport(po, proof.getServices());
    }

    @Override
    public final void run() {
	try {
	    JOptionPane.showMessageDialog(Main.getInstance(),
		    "File succesfully written to:\n" + createTestFile(),
		    "Creation finished", JOptionPane.INFORMATION_MESSAGE);
	} catch (final IOException e) {
	    e.printStackTrace();
	}
    }

    /**
     * Creates a class that is extended from the Class containing the method
     * that was chosen in the JMLSpecBrowser. Writes this class to a file.
     * 
     * @return The path where the file is stored
     * @throws IOException
     */
    @SuppressWarnings("unchecked")
    public final String createTestFile() throws IOException {

	final KeYJavaType supertypeKey = pm.getContainerType();

	final JavaInfo ji = proof.getJavaInfo();

	final ExtList l = new ExtList();

	// Add class frame
	// First add public modifier, then add name consisting of "Test" + old
	// class name
	// also adds the extends clause with source class as super class
	l.add(new Public());
	l.add(new ProgramElementName("Test" + className));

	final TypeReference supertype = new TypeRef(supertypeKey);
	l.add(new Extends(supertype));

	// Add all Constructors to l by iterating over all program methods
	// If the name of the current method equals "<init>" a new constructor
	// with the signature of the current method is added to l
	// Correct constructor is created by CreateMethod(met.getParameters(),
	// true)
        for (ProgramMethod programMethod : ji.getAllProgramMethods(
                supertypeKey)) {
            final ProgramMethod met = programMethod;
            if (met.getTypeReference() != null) {
                if (met.getTypeReference().equals(supertype)) {
                    if (met.getFullName().equals("<init>")) {
                        l.add(createMethod(met.getParameters(), true));
                    }
                }
            }
        }

	// Add the method to test
	l.add(createMethod(pm.getParameters(), false));

	// Create the wrapper class
	final ClassDeclaration classDecl = new ClassDeclaration(l,
	        new ProgramElementName("Test" + className), false);

	// Try to write the wrapper class to an StringWriter sw
	final StringWriter sw = new StringWriter();
	final PrettyPrinter pp = new CompilableJavaCardPP(sw, false);
	pp.printClassDeclaration(classDecl);
	return writeToFile(sw);
    }

    /**
     * Creates a method or a constructor with the parameters given in args,
     * depending on the parameter isConstructor. Body of method is just a call
     * of the source method Body of constructor is just a super call
     * 
     * @param args
     * @param isConstructor
     * @return MethodDeclaration or ConstructorDeclaration
     */
    @SuppressWarnings("unchecked")
    private final MethodDeclaration createMethod(
	    final ImmutableArray<? extends ParameterDeclaration> args,
	    final boolean isConstructor) {
	final ExtList l = new ExtList();

	// Choose name of method/constructor and add it to list
	// For a constructor, the name is the name of the class with prepended
	// "Test"
	// For method, the original name is get from
	// JMLMethodSpec.getMethodDeclaration().getName() and "test" is
	// prepended
	final String name;
	if (isConstructor) {
	    name = "Test" + className;
	} else {
	    name = "test" + pm.getName();
	}
	l.add(new ProgramElementName(name));

	// Iterates over the ArrayOf<n> args to get all
	// Parameters
	// ParameterDeclarations are added to list l so that new
	// method/constructor has correct numbers of parameters
	// Also adds correct parameters to params, so that the signature of
	// method/constructor that is called in body is correct
	final ExtList params = new ExtList();
	for (int i = 0; i < args.size(); i++) {
	    l.add(args.get(i));
	    params.add(args.get(i).getLastElement());
	}

	// Add the modifier public to method/constructor
	// Also adds modifier static if source method is static
	l.add(new Public());
	if (!isConstructor && pm.isStatic()) {
	    l.add(new Static());
	}

	// Add the specifications for the wrapper method
	if (!isConstructor) {
	    l.add(new Comment(getSpecs()));
	}

	// Choose name of method to call in body
	// For a constructor the super-constructor is called
	// For the method the source method is called
	// You get source method by
	// JMLMethodSpec.getMethodDeclaration().getName()
	final String calleeName;
	if (isConstructor) {
	    calleeName = "super";
	} else {
	    calleeName = pm.getName();
	}

	// Add return type and add the method body
	final StatementBlock mBody;
	// Return types just for methods, not for constructors
	if (!isConstructor) {
	    // For all non-void methods
	    // Wrapper method has the same return type as source method
	    // The source method is called in the return clause of wrapper
	    // method
	    if (!(pm.getTypeReference() == null)) {
		l.add(pm.getTypeReference());
		mBody = new StatementBlock(new Return(new MethodReference(
		        params, new ProgramElementName(calleeName), null)));

	    }
	    // For void methods
	    // If source method has no return type and no return clause
	    // Wrapper method also has no return type an no return clause
	    // The source method is called in body
	    else {

		mBody = new StatementBlock(new MethodReference(params,
		        new ProgramElementName(calleeName), null));

	    }
	}
	// For constructors
	// Constructors have no return type and no return clause
	// super constructor is called in body
	else {
	    mBody = new StatementBlock(new MethodReference(params,
		    new ProgramElementName(calleeName), null));

	}
	// Add the body/return to the method
	l.add(mBody);

	// Add throws Exception if needed
	l.add(pm.getThrown());

	// Return method/constructor
	if (isConstructor) {
	    return new ConstructorDeclaration(l, false);
	} else {
	    return new MethodDeclaration(l, false);
	}

    }

    /**
     * @return The a string of comments of the method chosen in JMLSpecBrowser
     *         _AND_ the additional information get from every not-closed goal
     */
    private final String getSpecs() {

	final StringBuffer result = new StringBuffer(
	        "/*@ public normal_behavior\n");

	// Get all OperationContracts for method from the
	// SpecificationRepositorie and converts them to an array
	final ImmutableSet<OperationContract> opCon = proof.getServices()
	        .getSpecificationRepository().getOperationContracts(pm);
	for (final OperationContract oc : opCon) {
	    if (oc instanceof OperationContractImpl) {

		// Append the requires term
		result.append("@ requires "
		        + (jmlEx.translate(((OperationContractImpl) oc)
		                .getOriginalPre().getFormula())) + ";");

		// Apend the ensures term
		result
		        .append("\n@ ensures "
		                + (jmlEx
		                        .translate(excFreeTerm(((OperationContractImpl) oc)
		                                .getOriginalPost().getFormula())))
		                + ";");
		// Append the concatinating 'also'
		result.append("\n@ also \n");
	    }
	}
	result.append(collectAllSpecs());
	result.append("@");
	return result.toString();
    }

    /**
     * Iterates through all open goals and creates an JML-comment of structure
     * 
     * @requires ...
     * @ensures ...
     * @also
     * @requires ...
     * @ensures ...
     * 
     *          where every open goal leads to a new block of specification with
     *          its generated requires- and ensures-clause
     * 
     * @return a StringBuffer
     */
    private final StringBuffer collectAllSpecs() {
	final StringBuffer result = new StringBuffer();

	final Iterator<Goal> iter = proof.openGoals().iterator();

	// Iterates through all open goals in current proof and creates term for
	// requires and ensures
	while (iter.hasNext()) {

	    // the current goal
	    final Goal currentGoal = iter.next();

	    // An iterator over the antecedent of the current goal
	    final Iterator<ConstrainedFormula> antIterator = currentGoal
		    .sequent().antecedent().toList().iterator();

	    // An iterator over the succedent of the current goal
	    final Iterator<ConstrainedFormula> sucIterator = currentGoal
		    .sequent().succedent().toList().iterator();

	    // The term, that represents the new requires-clause
	    Term requiresTerm = TermFactory.DEFAULT.createJunctorTerm(Op.TRUE);

	    // Iterates through the antecedent in current goal. Creates
	    // conjunction of the the elements
	    while (antIterator.hasNext()) {

		// The current constrained formula
		final ConstrainedFormula currentAnt = antIterator.next();

		// If current term is "inReachableState" or of structure *<.*>.*
		// (an implicite PO)
		// it is not conjuncted to the requires-term
		if (checkTerm(currentAnt.formula())) {
		    requiresTerm = TermFactory.DEFAULT.createJunctorTerm(
			    Op.AND, requiresTerm, currentAnt.formula());
		}
	    }

	    // flag for the structure { update }STOP!
	    boolean isInCorrectForm = false;

	    // Iterates through the succedent in current goal. Negates Terms
	    // and adds them to the term from the anteccedent
	    Term term = null;

	    // Iterates through the succedent in current goal. Creates
	    // conjunction of the elements
	    while (sucIterator.hasNext()) {

		// The current constrained formula
		final ConstrainedFormula suc = sucIterator.next();

		// Checks if the ConstrainedFormula has the structure { update
		// }STOP!.
		// In this case, we know, that the program of current goal is
		// completly symbolicly executed
		// So we set the flag isInCorrectForm.
		if (suc.formula().op() instanceof IUpdateOperator) {
		    final IUpdateOperator update = (IUpdateOperator) suc
			    .formula().op();
		    if ((update.target(suc.formula())).op().equals(
			    ComputeSpecification.ACCUMULATOR)) {
			term = suc.formula();
			isInCorrectForm = true;
		    }
		} else {

		    // Checks that the current formula is not the STOPTOKEN
		    if (!(suc.formula().op()
			    .equals(ComputeSpecification.ACCUMULATOR))) {

			// Checks that the current term is neither a Modality,
			// nor the "InReachableState" nor
			// an implicite proof obligation ( like <created> etc)
			if (checkTerm(suc.formula())
			        && !(suc.formula().op() instanceof IUpdateOperator)) {

			    // Negation of the current formula is added to the
			    // term of the requires clause
			    requiresTerm = TermFactory.DEFAULT
				    .createJunctorTerm(Op.AND, requiresTerm,
				            TermFactory.DEFAULT
				                    .createJunctorTerm(Op.NOT,
				                            suc.formula()));
			}
		    }

		}

	    }

	    // The correct result ist build

	    // The requires clause is allways written an consists of all
	    // formulas, that were in the
	    // antecedent and the negation of the formulas in the succedent
	    result
		    .append("@ requires " + jmlEx.translate(requiresTerm)
		            + ";\n");

	    // If the flag is true, we know, that there was a modality, that was
	    // completly symbolicaly executed
	    // So we could add all assignment pairs in the update to the ensures
	    // clause with structure following structure
	    // If there is an update {a :=b} the term a == \old(b) is add to the
	    // ensures clause
	    // If the flag is false the ensures clause just consists of true
	    if (isInCorrectForm) {
		result
		        .append("@ ensures "
		                + jmlEx.translate(cleanUpdate(term)));
	    } else {
		result.append("@ ensures true ");
	    }

	    // If there is another open goal, the "@ also" is added
	    if (iter.hasNext()) {
		result.append(";\n  @ also \n");
	    } else {
		result.append(";\n");
	    }

	}
	return result;
    }

    /**
     * Writes a classDeclaration contained in StringWriter sw to a file
     * 
     * @param sw
     *            the StringWriter where the class is stored
     * @return the path where the file was written
     * @throws IOException
     */
    private final String writeToFile(final StringWriter sw) throws IOException {

	// Select path or create new if not exist
	final File dir = new File(System.getProperty("user.home")
	        + File.separator + "JMLTestFiles");
	if (!dir.exists()) {
	    dir.mkdir();
	}

	// Create new File with correct name an path
	final File pcFile = new File(dir, "Test" + className + ".java");
	final String path = pcFile.getAbsolutePath();

	// Write content to file
	final BufferedWriter bw = new BufferedWriter(new FileWriter(pcFile));
	bw.write(sw.toString());
	bw.close();
	jmltfc.resetProperties();
	return path;
    }

    /**
     * Checks if the AssignementPairs of the given update are useful for our
     * task and returns an Update that just contains usefull Terms
     * 
     * @see de.uka.ilkd.key.jmltest.WrapperConstructor#checkTerm(Term)
     * @see de.uka.ilkd.key.jmltest.WrapperConstructor#isUsefulPair(AssignmentPair)
     * @param upTerm
     *            The Term thats needs to be cleaned up
     * @return An ArrayOf<s> containing only good Terms
     */
    private ImmutableArray<AssignmentPair> cleanUpdate(final Term upTerm) {

	final ImmutableArray<AssignmentPair> pairs = Update
	        .createUpdate(upTerm).getAllAssignmentPairs();

	final Vector<AssignmentPair> tmpVect = new Vector<AssignmentPair>();

	// Iterate over all existing Assignment pairs and adds good pairs in a
	// Vector
	for (int i = 0; i < pairs.size(); ++i) {
	    final AssignmentPair currPair = pairs.get(i);

	    if (checkTerm(currPair.locationAsTerm())
		    && checkTerm(currPair.value()) && isUsefulPair(currPair)) {
		tmpVect.add(currPair);
	    }
	}
	// If there is at least one good Term, create a new
	// ArrayOf<r> containing good terms
	if (tmpVect.size() > 0) {
	    final AssignmentPair[] tmp = new QuanAssignmentPairLazy[tmpVect
		    .size()];
	    for (int i = 0; i < tmpVect.size(); i++) {
		tmp[i] = tmpVect.elementAt(i);
	    }
	    return new ImmutableArray<AssignmentPair>(tmp);
	}
	// No good terms --> return empty Array
	return new ImmutableArray<AssignmentPair>();
    }

    /**
     * This method checks if we want this term for getting additional
     * information. TODO atm done by blacklisting, whitlisting is better
     * 
     * @param t
     *            The Term, to be checked
     * @return true if we want to keep this Term false else
     */
    private final boolean checkTerm(final Term t) {
	if (

	// Implicit condition for key
	t.op().toString().matches(".*<.*>.*") ||
	// The term InReachableState
	        t.op().equals(proof.getJavaInfo().getInReachableState()) ||
	        // InBound
	        proof.getServices().getTypeConverter().getIntLDT()
	                .getInBounds().equals(t.op()) ||
	        // We don't want Modalities
	        t.op() instanceof Modality ||
	        // We don't want Updates
	        t.op() instanceof IUpdateOperator
	        // We don't want anything like null.a
	        || ((t.op() instanceof AttributeOp) && (t.sub(0).op()
	                .equals(Op.NULL)))) {
	    return false;
	}
	// Iterates over all subterms
	for (int i = 0; i < t.arity(); i++) {
	    if (!(checkTerm(t.sub(i)))) {
		return false;
	    }
	}

	// Term must be good :)
	return true;
    }

    /**
     * This Method checks if both sides of an Assignment are useful
     * 
     * @see de.uka.ilkd.key.jmltest.WrapperConstructor#isUsefulPair(AssignmentPair)
     * @param currPair
     * @return true if pair is usefull false else
     */
    private final boolean isUsefulPair(final AssignmentPair currPair) {
	return (isUseful(currPair.locationAsTerm()) && isUseful(currPair
	        .value()));
    }

    /**
     * This method checks if the given Term is useful for our purpose. Primary
     * target is the filtering of local Variables cause those are not known
     * outside and would lead to errors if they occur in specification
     * 
     * @param t
     *            the Term to be checked
     * @return true if t is an Attribute, Parameter, \result, Constant; false
     *         else
     */
    private final boolean isUseful(final Term t) {

	if (t.op() instanceof LocationVariable) {
	    final LocationVariable tmp = (LocationVariable) t.op();
	    // We want Attributes, Parameters and the result of the term
	    // (\result)
	    if ((tmp.isMember())
		    || (po.getParams().contains(tmp))
		    || ((po.getResult() != null) && (po.getResult().equals(tmp)))) {

		return true;
	    }
	    // Other LocationVariables are local Variables, we don't like them
	    return false;
	}
	// Constants, Typecast are ok
	if ((t.op() instanceof CastFunctionSymbol)
	        || (t.op() instanceof RigidFunction)) {
	    return true;
	}
	assert false : "This location shall not be reached. Term: " + t
	        + " Op: " + t.op();
	return false;
    }

    /**
     * Checks if the last conjungt is the ExceptionTerm and removes this Term.
     * 
     * @param t
     *            The Term to be checked
     * @return A Term without the ExceptionTerm
     */
    private final Term excFreeTerm(final Term t) {
	if (t.op().equals(Op.AND)) {
	    final Term excTerm = t.sub(1);
	    if ((excTerm.op().equals(Op.EQUALS))
		    && (excTerm.sub(0).sort().equals(po.getExcVar().sort()) && (excTerm
		            .sub(1).op().equals(Op.NULL)))) {
		return t.sub(0);
	    }
	}
	assert false : ("DEBUG: Something wrong happend. It is assumed that the second subterm of the conjungtion originalPre is equals(exc,null). This is not the case at the moment. (excFreeTerm(Term t)@JMLTestFileCreator)");
	return t;
    }
}
