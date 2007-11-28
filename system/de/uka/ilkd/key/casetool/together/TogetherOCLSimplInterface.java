// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//
//

/** @author Daniel Larsson */

package de.uka.ilkd.key.casetool.together;

import java.io.IOException;
import java.util.Iterator;
import java.util.LinkedList;

import com.togethersoft.openapi.ide.IdeAccess;

import de.uka.ilkd.key.casetool.FunctionalityOnModel;
import de.uka.ilkd.key.casetool.HashMapOfClassifier;
import de.uka.ilkd.key.casetool.UMLOCLClassifier;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.TermSymbol;
import de.uka.ilkd.key.logic.op.oclop.OclOp;
import de.uka.ilkd.key.ocl.gf.ModelExporter;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.pp.NotationInfo;
import de.uka.ilkd.key.pp.PresentationFeatures;
import de.uka.ilkd.key.pp.ProgramPrinter;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.pp.StringBackend;

/** 
 * Used for OCL Simplification.
 * Wraps the machinery needed to, given a list of class names:  
 * <ol> 
 *  <li> Extract the model representation of these classes and
 *       invoke the prover machinery on these representations.
 *  </li>
 *  <li> Extract the resulting terms (simplified invariants),
 *       pretty-print them into strings, and update the source
 *       code of the proper classes with these invariants.
 * </li>
 * </ol>
 */
public class TogetherOCLSimplInterface {

    private Main main;
    private UMLOCLTogetherModel umlModel;

    public TogetherOCLSimplInterface() {}

    /** 
     * Performs the entire simplification.
     * @param newClasses List of class names (Strings), whose 
     * invariants need to be simplified.
     */
    public void simplifyConstraints(LinkedList newClasses) {
	IdeAccess.getIdeManager().saveAll();
	IdeAccess.getIdeManager().synchronize();

	//Create the file "../modelinfo.umltypes" needed for the "ocl2taclet" tool
	umlModel = new UMLOCLTogetherModel(null);
	createModelInfoFile();

	//For each of the newly created/changed classes (the elements of "newClasses"), 
	//check if it has an invariant and if so, simplify it.
	while (newClasses.size() > 0) {
	    String className = (String)newClasses.getFirst();
	    TogetherModelClass togetherClass
		= umlModel.getTogetherReprModelClass(className);

	    //If "togetherClass" has an invariant, continue with simplification
	    if (togetherClass != null
		&& togetherClass.getMyInv().trim().length() > 0) {
		simplifyInvariant(togetherClass, newClasses);
	    } else {
		newClasses.remove(className);
	    }
	}
    }

    /** 
     * Creates a file with information about the UML model
     * and places it in the directory of the current
     * Together project. Needed for the invocation of
     * "ocl2taclet".
     */
    private void createModelInfoFile() {
	HashMapOfClassifier hashMapOfCs = umlModel.getUMLOCLClassifiers();

	//Temporary "hack" to cope with bug in the parsing of the file
	// "../modelinfo.umltypes".
	LinkedList list = new LinkedList();
	Iterator iterator = hashMapOfCs.values().iterator();
	while (iterator.hasNext()) {
	    UMLOCLClassifier classifier = (UMLOCLClassifier)iterator.next();
	    String cName = classifier.getFullName();
	    if (cName.startsWith("java.util")) {
		list.add(classifier.getName());
	    }
	}
	Iterator newIter = list.iterator();
	while (newIter.hasNext()) {
	    hashMapOfCs.remove((String)newIter.next());
	}
	// ... end "hack"
	
	ModelExporter me = new ModelExporter(hashMapOfCs);
	me.export(UMLOCLTogetherModel.getTogetherProjectDir() + "/modelinfo.umltypes");
    }

    /** 
     * Invokes the prover.
     * @param togetherClass The representation of the class whose 
     * invariant is going to be simplified.
     * @param newClasses Names of classes whose invariants
     * still need to be simplified.
     */
    private void simplifyInvariant(TogetherModelClass togetherClass,
				   LinkedList newClasses) {
	String res = FunctionalityOnModel.simplifyInvariant(togetherClass);
	main = Main.getInstance();

	//Do not continue until the prover exits (different threads).	    
	while (main.isVisible()) {
	    synchronized (main.monitor) {
		try {
		    main.monitor.wait();		    
		} catch (InterruptedException e) {
		    e.printStackTrace();
		}
	    }
	}

	//Extract the simplified constraint
	Proof proof = main.mediator().getProof();
	Node node = proof.openGoals().iterator().next().node();
	Term term = node.sequent().succedent().getFirst().formula().sub(0);
	writeInvariantsToClasses(term, newClasses);
    }

    /**
     * Uses recursion to write the list of simplified
     * invariants back to the source code of the proper classes.
     */
    private void writeInvariantsToClasses(Term listOfInvariants,
					  LinkedList newClasses) {
	if (listOfInvariants.op() != OclOp.CONS_INV) {
	    return;
	}
	Term invariant = listOfInvariants.sub(0);

	//Find the together class corresponding to the OCL Classifier
	//which is the context for the invariant.
	String className = invariant.sub(0).op().name().toString();
	String fixedClassName = className.replace('~', '.');
	TogetherModelClass togetherClass
	    = umlModel.getTogetherReprModelClass(fixedClassName);

	//Get the actual invariant as a String
	String inv = extractInvariantFromTerm(invariant.sub(1));
	
	//Update the UML model with the simplified invariant
	if (togetherClass != null) {
	    togetherClass.setMyInv(inv);
	    newClasses.remove(fixedClassName);
	}

	//Continue in the list of invariants.
	writeInvariantsToClasses(listOfInvariants.sub(1), newClasses);
    }

    /** 
     * @param term The simplified invariant in form of a Term.
     * @return The same invariant as a String.
     */
    private String extractInvariantFromTerm(Term term) {
	TermSymbol oclWrapper = (Function)main.mediator()
	    .func_ns().lookup(new Name("$OclWrapper"));
	Term formula = TermFactory.DEFAULT
	    .createFunctionTerm(oclWrapper, term);
	StringBackend backend = new StringBackend(55);
	NotationInfo notInfo = NotationInfo.createInstance();

	//For pretty-printing of numbers. Have to refresh the NotationInfo (for some reason).
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("#")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("Z")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("0")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("1")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("2")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("3")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("4")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("5")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("6")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("7")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("8")));
	notInfo.createNumLitNotation((Operator)main.mediator().func_ns()
				     .lookup(new Name("9")));

	PresentationFeatures.ENABLED = true;
	PresentationFeatures.modifyNotationInfo(notInfo, main.mediator().func_ns());
	    
	LogicPrinter lp = new LogicPrinter(new ProgramPrinter(),
					   notInfo,
					   backend,
					   main.mediator().getServices());
	try {
	    lp.printTerm(formula);
	    backend.flush();
	} catch (IOException ioe) {
	    ioe.printStackTrace();
	}
	return backend.getString();
    }
}
