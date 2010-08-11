// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import java.util.*;

import de.uka.ilkd.key.collection.DefaultImmutableSet;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.Constraint;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.unittest.AssGenFac.AssignmentGenerator;
import de.uka.ilkd.key.unittest.testing.DataStorage;
import de.uka.ilkd.key.visualization.ExecutionTraceModel;
import de.uka.ilkd.key.visualization.ProofVisualization;
import de.uka.ilkd.key.visualization.TraceElement;
import de.uka.ilkd.key.visualization.VisualizationStrategyForTesting;

/**
 * Generates a unittest from a proof or a node in a proof-tree.
 */
public class UnitTestBuilder {

    protected final HashMap<Node, ExecutionTraceModel[]> node2trace;

    protected final Services serv;

    protected final Constraint uc;

    // the nodes containing trace ends that have already been processed by the
    // proof visualization
    protected final HashSet<Node> traceEndNodes;

    protected PackageReference pr;

    // mbender: This object is only needed to store certain values, that are
    // needed for the KeY junit tests
    protected final DataStorage dataForTest;

    // private int coverage;

    /**
     * In black-box testing we may want to allow execution traces that include
     * modal operators on which no method calls have been executed or modal
     * operators on which no symbolic execution has been applied at all. This
     * is, e.g., desired if the first statement is a method call, that we cannot
     * execute because it is a black-box. Set this attribute to true to allow
     * such traces for the test code extraction.
     */
    protected final boolean allowStartWithNonContextTraceElement = true;

    // iff true only terminated traces are considered for test case generation
    public static boolean requireCompleteExecution = false;
    
    /**The field determines which node to select for the path condition.
     * When generating tests for a proof branch, a program trace is computed on that branch.
     * If this field is false, then the original implementation from Christian Engel is used
     * where the last node on the trace is used as path condition. If this field
     * is true, then the node selected by the user (possibly end-node of the proof branch)
     * will be used as path condition. */
    public static boolean allowNonTraceNodeAsPathCond = false; 

    protected final Namespace pvn;

    protected final String directory = null;

    protected final boolean testing;
    
    /**The TestGenerator contains a thread object that is made accessible through this field. */
    public TestGenerator tg = null;
    
    public UnitTestBuilder(final Services serv, final Proof p,
	    final boolean testing) {
	this.serv = serv;
	node2trace = new HashMap<Node, ExecutionTraceModel[]>();
	uc = p.getUserConstraint().getConstraint();
	traceEndNodes = new HashSet<Node>();
	pvn = p.getNamespaces().programVariables();
	dataForTest = new DataStorage();
	this.testing = testing;
    }

    public UnitTestBuilder(final Services serv, final Proof p) {
	this(serv, p, false);
    }

    /**
     * Returns the program methods that are symbolically executed in the
     * implementation under test <code>p</code>.
     */
    public ImmutableSet<ProgramMethod> getProgramMethods(final Proof p) {
	final Iterator<Node> it = p.root().leavesIterator();
	ImmutableSet<ProgramMethod> result = DefaultImmutableSet
	        .<ProgramMethod> nil();
	while (it.hasNext()) {
	    getProgramMethods_ProgressNotification(result,false);
	    final Node n = it.next();
	    final ExecutionTraceModel[] tr = getTraces(n);
	    result = result.union(getProgramMethods(tr));
	}
	getProgramMethods_ProgressNotification(result,true);
	return result;
    }
    /**
     * This method is meant to be overwritten by UnitTestBuilderGUIInterface in order to report
     * the progress of the evaluation of the method getProgramMethods to the user.
     * @param result intermediate result so far
     * @param finished true when the final result is computed by getProgramMethods.
     */
    protected void getProgramMethods_ProgressNotification(ImmutableSet<ProgramMethod> result, boolean finished){ }

    protected ImmutableSet<ProgramMethod> getProgramMethods(
	    final ImmutableList<Node> nodes) {
	final Iterator<Node> it = nodes.iterator();
	ImmutableSet<ProgramMethod> result = DefaultImmutableSet
	        .<ProgramMethod> nil();
	while (it.hasNext()) {
	    final Node n = it.next();
	    final ExecutionTraceModel[] tr = getTraces(n);
	    result = result.union(getProgramMethods(tr));
	}
	
	return result;
    }

    protected ExecutionTraceModel[] getTraces(final Node n) {
	ExecutionTraceModel[] tr = node2trace.get(n);
	if (tr == null) {
	    final ProofVisualization pv = new ProofVisualization(n,
		    new VisualizationStrategyForTesting(serv), // new
		    // SimpleVisualizationStrategy(serv),
		    serv, traceEndNodes, true);
	    tr = pv.getVisualizationModel().getExecutionTraces();
	    node2trace.put(n, tr);
	}
	return tr;
    }

    protected HashSet<Position> getStatements(final ExecutionTraceModel[] tr) {
	final HashSet<Position> result = new HashSet<Position>();
	for (final ExecutionTraceModel element : tr) {
	    result.addAll(element.getExecutedStatementPositions());
	}
	return result;
    }

    /**
     * Creates unit tests for execution traces containing at least one of the
     * methods in pms. Only execution traces on branches that end with one of
     * the nodes iterated by <code>it</code> are considered.
     */
    protected String createTestForNodes(final Iterator<Node> it,
	    final ImmutableSet<ProgramMethod> pms) {
	String methodName = null;
	Statement[] code = null;
	Term oracle = null;
	final LinkedList<ModelGenerator> mgs = new LinkedList<ModelGenerator>();

	final StringBuffer noTraceReasons = new StringBuffer();// For better
	// exception
	// notification
	int minTraceLen = Integer.MAX_VALUE; // For better exception
	// notification
	int nodeCounter = 0;// For better exception notification

	final HashSet<Node> nodesAlreadyProcessed = new HashSet<Node>();

	ImmutableSet<ProgramVariable> pvs = null;

	// the statements occuring in the considered execution traces
	final HashSet<Position> statements = new HashSet<Position>();

	TestCodeExtractor tce = null;
	
	while (it.hasNext()) {
	  //The original node is not necessarily the node for which the test is generated. 
	  //Tests are generated generated for nodes where execution traces end. Otherwise no tests could be generated for a closed proof tree. 
	    final Node originalNode = it.next(); 
	    nodeCounter++;
	    
	    createTestForNodes_progressNotification0(nodeCounter, originalNode);


	    final ExecutionTraceModel[] tr = getTraces(originalNode);
	    // mbender: collect data for KeY junit tests (see
	    // TestTestGenerator,TestHelper)
	    dataForTest.addETM(tr);

	    statements.addAll(getStatements(tr));
	    int maxRating = -1;

	    minTraceLen = (minTraceLen > tr.length) ? tr.length : minTraceLen;
	    // boolean traceFound = false;
	    for (int i = 0; i < tr.length; i++) {
		final boolean ratingCond = tr[i].getRating() == 0;
		final boolean blockCompletelyExecutedCond = (!tr[i]
		        .blockCompletelyExecuted() && requireCompleteExecution);
		final boolean infeasibleCond = (!tr[i].blockCompletelyExecuted())
		        			&& originalNode.isClosed();
		final boolean programMethodsNumCond = 
		    	tr[i].getProgramMethods(serv).union(pms).size() == 
		    	    tr[i].getProgramMethods(serv).size() + pms.size();
		final boolean nodeAlreadyProcessedCond = 
		    	nodesAlreadyProcessed.contains(tr[i].getLastTraceElement().node());
		final boolean inAntecCond = tr[i].getLastTraceElement().isInAntec();
		final boolean noContextTraceElementCond = (tr[i]
		        .getFirstContextTraceElement() == TraceElement.END && !allowStartWithNonContextTraceElement);
		boolean nullPointer=true; 
		try{
		    tr[i].getFirstTraceElement().getPosOfModality().subTerm().sub(0);
		    nullPointer = false;
		}catch(Exception ex){
		    nullPointer = true;
		}
		// boolean executionTraceTypeCond = tr[i].getType() !=
		// ExecutionTraceModel.TYPE1;
		if (ratingCond || blockCompletelyExecutedCond || infeasibleCond
		        || programMethodsNumCond || nodeAlreadyProcessedCond
		        || inAntecCond || noContextTraceElementCond
		        || nullPointer
		// || executionTraceTypeCond
		) {
		    noTraceReasons.append("---------------------\nNode["
			    + tr[i].getLastTraceElement().node().serialNr()
			    + "],Trace[" + i + "]\n");
		    if (ratingCond) {
			noTraceReasons.append(" -Trace has rating 0.\n");
		    }
		    if (blockCompletelyExecutedCond) {
			noTraceReasons
			        .append(" -JavaBlock wasn't completely executed but complete execution is selected.\n");
		    }
		    if (infeasibleCond) {
			noTraceReasons
			        .append(" -Path is infeasible, i.e. Path condition not satisfiable.\n");
		    }
		    if (programMethodsNumCond) {
			noTraceReasons
			        .append(" -TODO:There is a problem with the number of program methods:"
			                + "\n   tr[i].getProgramMethods(serv).size()="
			                + tr[i].getProgramMethods(serv).size()
			                + "\n   pms.size()="
			                + pms.size()
			                + "\n   the sum is:"
			                + (tr[i].getProgramMethods(serv).size() + pms
			                        .size()) + "\n");
		    }
		    if (nodeAlreadyProcessedCond) {
			noTraceReasons.append(" -Node is already prodessed.\n");
		    }
		    if (inAntecCond) {
			noTraceReasons
			        .append(" -JavaBlock is not in the succeedent of the sequent\n");
		    }
		    if (noContextTraceElementCond) {
			noTraceReasons
			        .append(" -No ContextTraceElement was found like, e.g., a method-frame.\n");
		    }
		    if (nullPointer){
			noTraceReasons
		        .append(" -Null pointer occured during evaluation of \ntr[i].getFirstTraceElement().getPosOfModality().subTerm().sub(0).\n");
		    }
		    continue;
		}
		// nodesAlreadyProcessed.add(tr[i].getLastTraceElement().node());
		if (maxRating == -1
		        || tr[i].getRating() > tr[maxRating].getRating()) {
		    maxRating = i;
		}
		if (tg == null) {
		    final AssignmentGenerator ag = new AssGenFac().create();
		    tce = new TestCodeExtractor(tr[i], serv, pvn, ag);
		    code = tce.extractTestCode();
		    final JavaASTCollector coll = new JavaASTCollector(
			    new StatementBlock(code), MethodFrame.class);
		    coll.start();
		    if (coll.getNodes().size() == 0) {

			//There are "GUI interface" versions of the classes UnitTestBuilder and TestGenerator.
			if(this instanceof UnitTestBuilderGUIInterface ){
			    UnitTestBuilderGUIInterface thisGUI = (UnitTestBuilderGUIInterface) this;
				tg = new TestGenFac().create(serv, "Test"
				        + tce.getFileName(), directory, testing, ag,
				        new TestGeneratorGUIInterface());
			    tg.gui.setMethodSelectionDialog(thisGUI.dialog); //A big clumsy. 
			}else{
				tg = new TestGenFac().create(serv, "Test"
				        + tce.getFileName(), directory, testing, ag,
				        null);			    
			}
			if (methodName == null) {
			    methodName = tce.getMethodName();
			}
			oracle = tce.getTermForOracle();
			pvs = tce.getNewProgramVariables();
			// tr[i].getFirstTraceElement().
			// node().getGlobalProgVars().
			// union(tce.getNewProgramVariables());
			//tce.getNewProgramVariables();
			pr = tce.getPackage();
		    }
		}
	    }//for
	    if (maxRating != -1) {
		Node pathConditionNode = null;
		if(!allowNonTraceNodeAsPathCond){
		    pathConditionNode = tr[maxRating].getLastTraceElement().node();
		}else{
		    pathConditionNode = originalNode;
		}
		createTestForNodes_progressNotification1(tr[maxRating], pathConditionNode, originalNode);
		mgs.add(getModelGenerator(tr[maxRating].toString(),
					  pathConditionNode, 
					  originalNode));
		nodesAlreadyProcessed.add(tr[maxRating].getLastTraceElement().node());
	    }
	}
	if (methodName == null) {
	    String pmsStr = "";
        for (ProgramMethod pm1 : pms) {
            final ProgramMethod pm = pm1;
            pmsStr += pm.getName() + "\n";
        }
	    
	    //The following call throws an exception if it is not overwritten. 
	    createTestForNodes_progressNotification2(new UnitTestException(
		    "No suitable Execution Trace was found. "
		            + "The reasons for filtering out traces were:\n"
		            + (nodeCounter == 0 ? "-Number of inspected nodes is 0\n"
		                    : "")
		            + noTraceReasons
		            + "========================\nThe regarded program methods were:\n"
		            + (pms.size() == 0 ? "There are no program methods!\n"
		                    : pmsStr)
		            + (minTraceLen <= 1 ? "(warning: the longest trace has length:"
		                    + minTraceLen + ")\n"
		                    : "")));
	}
	// mbender: collect data for KeY junit tests (see
	// TestTestGenerator,TestHelper)
	dataForTest.setPms(pms);
	dataForTest.setNodeCount(nodeCounter);
	dataForTest.setCode(code);
	dataForTest.setOracle(oracle);
	dataForTest.setNrOfMgs(mgs.size());
	dataForTest.setPvs(pvs);
	dataForTest.setTg(tg);
	tg.setData(dataForTest);
	// computeStatementCoverage(statements, tce.getStatements());
	 String filename = tg.generateTestSuite(code, oracle, mgs, pvs,"test" + methodName, pr);
	 tg.clean();
	 tg = null;
	 return filename;
    }
    
    /** called by createTestForNodes. Should be overwritten by UnitTestBuilderGUIInterface to
     * notify the user about the progress of the computation.*/
    protected void createTestForNodes_progressNotification0(int nodeCounter, Node n){
	//System.out.println("("+nodeCounter+") Searching for suitable trace for node "+n.serialNr());
	return;
    }

    /** called by createTestForNodes. Should be overwritten by UnitTestBuilderGUIInterface to
     * notify the user about the progress of the computation.*/
    protected void createTestForNodes_progressNotification1(ExecutionTraceModel etm, Node pathConditionNode, Node originalNode){
	//System.out.println("Selected node with path condition is "+pathConditionNode.serialNr()+" for child node "+originalNode.serialNr());
	return;
    }
    /** called by createTestForNodes. Should be overwritten by UnitTestBuilderGUIInterface to
     * notify the user about the progress of the computation.*/
    protected void createTestForNodes_progressNotification2(UnitTestException e){
	throw e;
    }

    /**
     * Creates a Unittest for the node <code>n</code>. The testdata is derived
     * only from <code>n</code>.
     */
    public String createTestForNode(final Node n) {
	final ExecutionTraceModel[] tr = getTraces(n);
	return createTestForNodes(Arrays.asList(n).iterator(),
	        getProgramMethods(tr));
    }

    public String createTestForNodes(final ImmutableList<Node> l) {
	return createTestForNodes(l.iterator(), getProgramMethods(l));
    }

    // protected void computeStatementCoverage(HashSet<Position>
    // executedStatements,
    // HashSet<Statement> sourceStatements) {
    // if (sourceStatements.size() == 0) {
    // coverage = -1;
    // } else {
    // int i = 0;
    // Iterator<Statement> it = sourceStatements.iterator();
    // while (it.hasNext()) {
    // if (executedStatements.contains(it.next().getPositionInfo()
    // .getStartPosition())) {
    // i++;
    // }
    // }
    // coverage = (100 * i) / sourceStatements.size();
    // }
    // }

    protected boolean isInteresting(final ExecutionTraceModel tr) {
	return tr.getRating() != 0 && !tr.getLastTraceElement().isInAntec()
	        && (!requireCompleteExecution || tr.blockCompletelyExecuted());
    }

    protected ImmutableSet<ProgramMethod> getProgramMethods(
	    final ExecutionTraceModel[] traces) {
	ImmutableSet<ProgramMethod> result = DefaultImmutableSet
	        .<ProgramMethod> nil();
	for (final ExecutionTraceModel trace : traces) {
	    if (isInteresting(trace)) {
		result = result.union(trace.getProgramMethods(serv));
	    }
	}
	return result;
    }

    // /**
    // * Returns the percentage of covered statements.
    // */
    // public int getStatementCoverage() {
    // return coverage;
    // }

    /**
     * Creates a Unittest for the proof <code>p</code>. The testdata is derived
     * from the leaves of <code>p</code>'s proof tree.
     */
    public String createTestForProof(final Proof p) {
	return createTestForNodes(p.root().leavesIterator(),
	        getProgramMethods(p));
    }

    /**
     * Creates a Unittest for those branches in the proof tree of <code>p</code>
     * on which at least one of the program methods in pms is symbolically
     * executed. The testdata is derived from the leaves of <code>p</code>'s
     * proof tree.
     */
    public String createTestForProof(final Proof p,
	    final ImmutableSet<ProgramMethod> pms) {
	return createTestForNodes(p.root().leavesIterator(), pms);
    }

    /**This method is overwritten by UnitTestGuilderGUIInterface where ModelGeneratorGUIInterface is returned.
     * @param node this is the node for which a counter example is generated.
     * @param originalNode this may be a leaf node below {@code node}. 
      */
    protected ModelGenerator getModelGenerator(final String executionTraceModel, final Node node,
	    final Node originalNode) {
	return new ModelGenerator(serv, uc, node, executionTraceModel, originalNode);
    }

    public DataStorage getDS() {
	return dataForTest;
    }
   
}
