// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.util.HashSet;
import java.util.Iterator;

import de.uka.ilkd.key.collection.*;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.unittest.AssGenFac.AssignmentGenerator;
import de.uka.ilkd.key.visualization.ExecutionTraceModel;
import de.uka.ilkd.key.visualization.TraceElement;

/**
 * Extracts the code, for which we want to create a unittest, from a formula of
 * the form: &lt updates&gt \\&lt code\\&gt post.
 */
public class TestCodeExtractor {

    private final ExecutionTraceModel tr;
    private final Services serv;

    private final Namespace pvn;

    private final AssignmentGenerator ag;

    private Statement[] testCode = null;

    private Term post = null;

    private PackageReference context = null;

    private StatementBlock sb = null;

    // the name of the file the method under test is located in
    private String fileName = null;

    // the package of the containing class
    // private String packageName = null;
    // the method we want to test
    private String methodName = null;

    private static int testCounter = 0;

    private Namespace newPVs = new Namespace();

    private NRFLHandler nrflHan;

    public TestCodeExtractor(final ExecutionTraceModel tr, final Services serv,
	    final Namespace pvn, final AssignmentGenerator ag) {
	this.tr = tr;
	this.serv = serv;
	this.pvn = pvn;
	this.ag = ag;
    }

    // MAYBE OBSOLETE
    // public Statement[] extractTestCode(){
    // if(testCode != null){
    // return testCode;
    // }
    // Semisequent succ = getNodeForCodeExtraction(tr).sequent().succedent();
    // for(int i=0; i<succ.size(); i++){
    // Term current = new NRFLtoProgVar().transform(succ.get(i).formula());
    // IList<Statement> statements = ImmSLList.<Statement>nil();
    // //TODO: Resolve data dependencies in simultaneous updates.
    // while(current.op() instanceof IUpdateOperator){
    // statements = statements.append(getAssignments(current));
    // current = current.sub(current.op().arity()-1);
    // }
    // if(current.op() instanceof Modality){
    // post = current.sub(0);
    // sb = (StatementBlock) current.javaBlock().program();
    // collectUndeclaredVariables(sb);
    // statements = statements.append(flatten(sb));
    // testCode = statements.toArray();
    // return testCode;
    // }
    // }
    // throw new NotTranslatableException("Could not extract testcode");
    // }

    public Statement[] extractTestCode() {
	if (testCode != null) {
	    return testCode;
	}
	final TraceElement trace = tr.getFirstTraceElement();
	nrflHan = new NRFLHandler(serv, this, trace.getPosOfModality());

	Term current = nrflHan.getResult();
	ImmutableList<Statement> statements = ImmutableSLList.<Statement> nil();
	// TODO: Resolve data dependencies in simultaneous updates.
	while (current.op() instanceof IUpdateOperator) {
	    statements = statements.append(getAssignments(current));
	    current = current.sub(current.op().arity() - 1);
	}
	if (current.op() instanceof Modality) {
	    post = current.sub(0);
	    sb = (StatementBlock) trace.getProgram();
	    collectUndeclaredVariables(sb);
	    statements = statements.append(flatten(sb));
	    testCode = statements.toArray(new Statement[statements.size()]);
	    return testCode;
	}
	throw new NotTranslatableException("Could not extract testcode");
    }

    /**
     * Collects variables not explicitely declared in the IUT.
     */
    private void collectUndeclaredVariables(final StatementBlock stb) {
	JavaASTCollector coll = new JavaASTCollector(stb, ProgramVariable.class);
	coll.start();
	ImmutableList<ProgramElement> l = coll.getNodes();
	Iterator<ProgramElement> it = l.iterator();
	while (it.hasNext()) {
	    final ProgramVariable pv = (ProgramVariable) it.next();
	    if (pvn.lookup(pv.name()) == pv) {
		newPVs.add(pv);
	    }
	}
	coll = new JavaASTCollector(stb, LocalVariableDeclaration.class);
	coll.start();
	l = coll.getNodes();
	coll = new JavaASTCollector(stb, ParameterDeclaration.class); // chrisg:14.5.2009;
	// The
	// argument
	// in the
	// head of
	// a
	// catch-block
	// is a
	// ParameterDeclaration.
	// If
	// declarations
	// are
	// missing
	// in the
	// generated
	// test
	// file,
	// then try
	// to
	// remove
	// this
	// code.
	coll.start();
	if (l.isEmpty()) {
	    l = coll.getNodes(); // Warningg l.append(coll.getNodes()) does not
	    // give the expected result.
	} else {
	    l.append(coll.getNodes());
	}

	it = l.iterator();
	ImmutableList<Named> lon = newPVs.allElements();
	while (it.hasNext()) {
	    ImmutableArray<VariableSpecification> vars = null;
	    final Object pvDecl = it.next();
	    if (pvDecl instanceof LocalVariableDeclaration) {
		final LocalVariableDeclaration lvd = (LocalVariableDeclaration) pvDecl;
		vars = lvd.getVariables();
	    } else if (pvDecl instanceof ParameterDeclaration) {
		final ParameterDeclaration pd = (ParameterDeclaration) pvDecl;
		vars = pd.getVariables();
	    }
	    for (int i = 0; i < vars.size(); i++) {
		final IProgramVariable pv = vars.get(i).getProgramVariable();
		if (pvn.lookup(pv.name()) == pv) {
		    lon = lon.removeAll(pv);
		}
	    }
	}
	newPVs = new Namespace();
	while (!lon.isEmpty()) {
	    newPVs.add(lon.head());
	    lon = lon.tail();
	}
    }

    public HashSet<Statement> getStatements() {
	if (sb != null) {
	    return getStatements(sb);
	}
	return new HashSet<Statement>();
    }

    private HashSet<Statement> getStatements(final StatementBlock sbl) {
	final HashSet<Statement> result = new HashSet<Statement>();
	for (int i = 0; i < sbl.getChildCount(); i++) {
	    final Statement s = sbl.getStatementAt(i);
	    if (s instanceof StatementBlock) {
		result.addAll(getStatements((StatementBlock) s));
	    } else if (s instanceof MethodBodyStatement) {
		final JavaASTCollector coll = new JavaASTCollector(
		        ((MethodBodyStatement) s).getBody(serv),
		        Statement.class);
		coll.start();
		final ImmutableList<ProgramElement> l = coll.getNodes();
		final Iterator<ProgramElement> it = l.iterator();
		while (it.hasNext()) {
		    final Statement next = (Statement) it.next();
		    if (!(next instanceof StatementContainer)) {
			result.add(next);
		    }
		}
	    } else {
		result.add(s);
	    }
	}
	return result;
    }

    public Node getNodeForCodeExtraction(final ExecutionTraceModel etr) {
	Node node = etr.getFirstTraceElement().node();
	while (!node.root()) {
	    node = node.parent();
	}
	while (node.childrenCount() == 1
	        && node != etr.getFirstTraceElement().node()) {
	    node = node.child(0);
	}
	return node;
    }

    private ImmutableList<Statement> flatten(final StatementBlock stb) {
	ImmutableList<Statement> result = ImmutableSLList.<Statement> nil();
	for (int i = 0; i < stb.getStatementCount(); i++) {
	    if (fileName == null) {
		fileName = stb.getStatementAt(i).getPositionInfo()
		        .getFileName();
	    }
	    if (stb.getStatementAt(i) instanceof StatementBlock) {
		result = result.append(flatten((StatementBlock) stb
		        .getStatementAt(i)));
	    } else if (stb.getStatementAt(i) instanceof MethodBodyStatement) {
		result = result
		        .append(convertMBSToMethodCall((MethodBodyStatement) stb
		                .getStatementAt(i)));
	    } else {
		result = result.append(stb.getStatementAt(i));
	    }
	}
	return result;
    }

    /**
     * Returns the formula from which an oracle for the extracted code can be
     * created.
     */
    public Term getTermForOracle() {
	if (post == null) {
	    extractTestCode();
	}
	return post;
    }

    /**
     * Returns the package the code under test is located in.
     */
    public PackageReference getPackage() {
	if (context == null) {
	    extractTestCode();
	}
	return context;
    }

    /**
     * Transforms updates into assignment expressions.
     */
    private ImmutableList<Statement> getAssignments(final Term t) {
	ImmutableList<Statement> result = ImmutableSLList.<Statement> nil();
	final IUpdateOperator uop = (IUpdateOperator) t.op();
	Term currLoc;
	for (int i = 0; i < uop.locationCount(); i++) {
	    currLoc = uop.location(t, i);
	    if (currLoc.op() instanceof NonRigidFunctionLocation) {
		result = result.append(nrflHan.getWriteRep(currLoc));
	    } else {
		Expression l, r;
		l = convertToProgramElement(currLoc);
		r = convertToProgramElement(uop.value(t, i));
		result = result.append(ag.assignmentOrSet(l, r, serv));
	    }
	}
	return result;
    }

    public Expression convertToProgramElement(Term t) {
	t = TestGenerator.replaceConstants(t, serv, newPVs);
	return serv.getTypeConverter().convertToProgramElement(t);
    }

    /**
     * Returns the program variables newly introduced as substitution for skolem
     * constants and those found in the IUT.
     */
    public ImmutableSet<ProgramVariable> getNewProgramVariables() {
	ImmutableSet<ProgramVariable> result = DefaultImmutableSet
	        .<ProgramVariable> nil();
	final Iterator<Named> it = newPVs.allElements().iterator();
	while (it.hasNext()) {
	    result = result.add((ProgramVariable) it.next());
	}
	return result;
    }

    private Statement convertMBSToMethodCall(final MethodBodyStatement mbs) {
	methodName = mbs.getProgramMethod(serv).getMethodDeclaration()
	        .getName();
	final String sortName = mbs.getProgramMethod(serv).getContainerType()
	        .getSort().name().toString();
	fileName = sortName.substring(sortName.lastIndexOf(".") + 1, sortName
	        .length());
	// if(sortName.lastIndexOf(".")!=-1){
	// packageName = sortName.substring(0, sortName.lastIndexOf("."));
	// }
	final MethodReference mr = new MethodReference(mbs.getArguments(),
	        new ProgramElementName(mbs.getProgramMethod(serv).getName()),
	        mbs.getProgramMethod(serv).isStatic() ? new TypeRef(mbs
	                .getProgramMethod(serv).getContainerType()) : mbs
	                .getDesignatedContext());
	context = mbs.getProgramMethod(serv).getContainerType()
	        .createPackagePrefix();
	if (mbs.getResultVariable() != null) {
	    final ProgramVariable rv = (ProgramVariable) mbs
		    .getResultVariable();
	    newPVs.add(rv);
	    return new CopyAssignment(rv, mr);
	} else {
	    return mr;
	}
    }

    public String getFileName() {
	return (fileName == null ? "Generic" : fileName) + (testCounter++);
    }

    // public String getPackageName(){
    // return packageName;
    // }

    public String getMethodName() {
	return (methodName == null ? "code" : methodName);
    }

}
