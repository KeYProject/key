package de.uka.ilkd.key.unittest;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTCollector;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.visualization.*;

import java.util.*;

/**
 * Generates a unittest from a proof or a node in a proof-tree.
 */
public class UnitTestBuilder{

    private HashMap node2trace;

    private Services serv;
    private Constraint uc;
    // the nodes containing trace ends that have already been processed by the
    // proof visualization
    private HashSet traceEndNodes;
    private PackageReference pr;
    private int coverage;
    
    /**In black-box testing we may want to allow execution traces that include 
     * modal operators on which no method calls have been executed 
     * or modal operators on which no symbolic execution has been applied at all.
     * This is, e.g., desired if the first statement is a method call, that we cannot execute 
     * because it is a black-box. Set this attribute to true to allow such traces for
     * the test code extraction.*/
    private boolean allowStartWithNonContextTraceElement=true;

    // iff true only terminated traces are considered for test case generation
    public static boolean requireCompleteExecution=false;

    public Namespace pvn;

    private String directory=null;

    public UnitTestBuilder(Services serv, Proof p){
	this.serv = serv;
	node2trace = new HashMap();
	uc = p.getUserConstraint().getConstraint();
	traceEndNodes = new HashSet();
	pvn = p.getNamespaces().programVariables();
    }
    
    public UnitTestBuilder(Services serv, Proof p, String directory){
        this(serv,p);
        this.directory=directory;        
    }

    /**
     * Returns the program methods that are symbolically executed in the
     * implementation under test <code>p</code>.
     */
    public SetOfProgramMethod getProgramMethods(Proof p){
	Iterator<Node> it = p.root().leavesIterator();
	SetOfProgramMethod result = SetAsListOfProgramMethod.EMPTY_SET;
	while(it.hasNext()){
	    Node n = it.next();
	    ExecutionTraceModel[] tr = getTraces(n);
	    result = result.union(getProgramMethods(tr));
	}
	return result;
    }

    
    public SetOfProgramMethod getProgramMethods(ListOfNode nodes){
        IteratorOfNode it = nodes.iterator();
        SetOfProgramMethod result = SetAsListOfProgramMethod.EMPTY_SET;
        while(it.hasNext()){
            Node n = it.next();
            ExecutionTraceModel[] tr = getTraces(n);
            result = result.union(getProgramMethods(tr));
        }
        return result;
    }

    
    
    private ExecutionTraceModel[] getTraces(Node n){
	ExecutionTraceModel[] tr = (ExecutionTraceModel[]) node2trace.get(n);
	if(tr == null){
	    ProofVisualization pv = 
		new ProofVisualization(n, 
                new VisualizationStrategyForTesting(serv),
                serv, traceEndNodes, true);
	    tr = pv.getVisualizationModel().getExecutionTraces();
	    node2trace.put(n, tr);
	}
	return tr;
    }

    private HashSet getStatements(ExecutionTraceModel[] tr){
	HashSet result = new HashSet();
	for(int i=0; i<tr.length; i++){
	    result.addAll(tr[i].getExecutedStatementPositions());
	}
	return result;
    }

    /**
     * Creates unit tests for execution traces containing at least one
     * of the methods in pms. Only execution traces on branches that end with
     * one of the nodes iterated by <code>it</code> are considered.  
     */
    private String createTestForNodes(Iterator<Node> it, 
				      SetOfProgramMethod pms){
	TestGenerator tg = null;
	String methodName = null;
	Statement[] code = null;
	Term oracle = null;
	LinkedList mgs = new LinkedList();
    
    StringBuffer noTraceReasons = new StringBuffer();//For better exception notification
    int minTraceLen = Integer.MAX_VALUE; //For better exception notification
    int nodeCounter = 0;//For better exception notification
	
	HashSet nodesAlreadyProcessed = new HashSet();

	SetOfProgramVariable pvs = null;

	// the statements occuring in the considered execution traces
	HashSet statements = new HashSet();

	TestCodeExtractor tce = null;

	while(it.hasNext()){
	    Node n = it.next();
        nodeCounter++;

	    ExecutionTraceModel[] tr = getTraces(n);
	    
	    statements.addAll(getStatements(tr));
	    int maxRating = -1;

	    minTraceLen = (minTraceLen>tr.length)?tr.length:minTraceLen;
//	    boolean traceFound = false; 
	    for(int i=0; i<tr.length; i++){
            boolean ratingCond = tr[i].getRating()==0;
            boolean blockCompletelyExecutedCond = (!tr[i].blockCompletelyExecuted() &&
                                                   requireCompleteExecution); 
            boolean infeasibleCond = (!tr[i].blockCompletelyExecuted()) && n.isClosed();
            boolean programMethodsNumCond =            
                            tr[i].getProgramMethods(serv).union(pms).size() == 
                            tr[i].getProgramMethods(serv).size()+pms.size();
            boolean nodeAlreadyProcessedCond = 
                        nodesAlreadyProcessed.contains(tr[i].getLastTraceElement().node());
            boolean inAntecCond = tr[i].getLastTraceElement().isInAntec();
            boolean noContextTraceElementCond = 
                        (tr[i].getFirstContextTraceElement() == TraceElement.END
                        && !allowStartWithNonContextTraceElement);
            //boolean executionTraceTypeCond = tr[i].getType() != ExecutionTraceModel.TYPE1; 
    		if(ratingCond || blockCompletelyExecutedCond ||
    		    infeasibleCond || programMethodsNumCond ||
                nodeAlreadyProcessedCond || inAntecCond ||
                noContextTraceElementCond
                //|| executionTraceTypeCond
                ){
                noTraceReasons.append("---------------------\nNode["+
                            tr[i].getLastTraceElement().node().serialNr()+
                            "],Trace["+i+"]\n");
                if(ratingCond)noTraceReasons.append(" -Trace has rating 0.\n");
                if(blockCompletelyExecutedCond)noTraceReasons.append(" -JavaBlock wasn't completely executed but complete execution is selected.\n");
                if(infeasibleCond)noTraceReasons.append(" -Path is infeasible, i.e. Path condition not satisfiable.\n");
                if(programMethodsNumCond)
                    noTraceReasons.append(" -TODO:There is a problem with the number of program methods:"+
                            "\n   tr[i].getProgramMethods(serv).size()="+tr[i].getProgramMethods(serv).size()+
                            "\n   pms.size()="+pms.size()+
                            "\n   the sum is:"+(tr[i].getProgramMethods(serv).size()+pms.size())+"\n");
                if(nodeAlreadyProcessedCond)noTraceReasons.append(" -Node is already prodessed.\n");
                if(inAntecCond)noTraceReasons.append(" -JavaBlock is not in the succeedent of the sequent\n");
                if(noContextTraceElementCond)noTraceReasons.append(" -No ContextTraceElement was found like, e.g., a method-frame.\n");
    		    continue;
    		}
//		nodesAlreadyProcessed.add(tr[i].getLastTraceElement().node());
		if(maxRating == -1 || 
		   tr[i].getRating()>tr[maxRating].getRating()){
		       maxRating = i;
		}
		if(tg == null){
		    tce = new TestCodeExtractor(tr[i], serv, pvn);
		    code = tce.extractTestCode();
		    JavaASTCollector coll = 
			new JavaASTCollector(new StatementBlock(code), 
					     MethodFrame.class);
		    coll.start();
		    if(coll.getNodes().size()==0){
			tg = new TestGenerator(serv, "Test"+tce.getFileName(),directory);
			if(methodName == null){
			    methodName = tce.getMethodName();
			}
			oracle = tce.getTermForOracle();
			pvs = tce.getNewProgramVariables();
			//tr[i].getFirstTraceElement().
			    //node().getGlobalProgVars().
			    //union(tce.getNewProgramVariables());
			    tce.getNewProgramVariables();
			pr = tce.getPackage();
		    }
		}
	    }
	    if(maxRating!=-1){
		mgs.add(getModelGenerator(tr[maxRating],n));
		nodesAlreadyProcessed.add(tr[maxRating].
					  getLastTraceElement().node());
	    }
	}
	if(methodName==null){
        String pmsStr="";
        IteratorOfProgramMethod pmIt = pms.iterator();
        while(pmIt.hasNext()){
            ProgramMethod pm = pmIt.next();
            pmsStr += pm.getName() + "\n";
        }
        
	    throw new UnitTestException("No suitable Execution Trace was found. " +
                "The reasons for filtering out traces were:\n"+
                (nodeCounter==0? "-Number of inspected nodes is 0\n":"") +
                noTraceReasons+
                "========================\nThe regarded program methods were:\n"+
                (pms.size()==0?"There are no program methods!\n":pmsStr)+
                (minTraceLen<=1 ? 
                        "(warning: the longest trace has length:"+minTraceLen+")\n": ""));
	}
	computeStatementCoverage(statements, tce.getStatements());
	tg.generateTestSuite(code, oracle, mgs, pvs, "test"+methodName, pr);
	return tg.getPath();
    }

    /**
     * Creates a Unittest for the node <code>n</code>. The testdata is derived
     * only from <code>n</code>.
     */
    public String createTestForNode(Node n){
	ExecutionTraceModel[] tr = getTraces(n);
	return createTestForNodes(Arrays.asList(n).iterator(), getProgramMethods(tr));
    }
    
    
    public String createTestForNodes(ListOfNode l){        
        return createTestForNodes(Arrays.asList(l.toArray()).iterator(), 
                getProgramMethods(l));
    }


    private void computeStatementCoverage(HashSet executedStatements,
					  HashSet sourceStatements){
	if(sourceStatements.size()==0){
	    coverage = -1;
	}else{
	    int i = 0;
	    Iterator it = sourceStatements.iterator();
	    while(it.hasNext()){
                Statement s = (Statement) it.next();
		if(executedStatements.contains(
		       s.getPositionInfo().getStartPosition())){
		    i++;
		}
	    }
	    coverage = (100*i)/sourceStatements.size();
	}
    }

    private boolean isInteresting(ExecutionTraceModel tr){
	return tr.getRating()!=0 && 
	    !tr.getLastTraceElement().isInAntec() &&
	    (!requireCompleteExecution || tr.blockCompletelyExecuted());
    }

    private SetOfProgramMethod getProgramMethods(ExecutionTraceModel[] traces){
	SetOfProgramMethod result = SetAsListOfProgramMethod.EMPTY_SET;
	for(int i=0; i<traces.length; i++){
	    if(isInteresting(traces[i])){
		result = result.union(traces[i].getProgramMethods(serv));
	    }
	}
	return result;
    }

    /**
     * Returns the percentage of covered statements.
     */
    public int getStatementCoverage(){
	return coverage;
    } 

    /**
     * Creates a Unittest for the proof <code>p</code>. The testdata is derived
     * from the leaves of <code>p</code>'s proof tree.
     */
    public String createTestForProof(Proof p){
	return createTestForNodes(p.root().leavesIterator(), getProgramMethods(p));
    }

    /**
     * Creates a Unittest for those branches in the proof tree of
     * <code>p</code> on which at least one of the program methods in pms is
     * symbolically executed. 
     * The testdata is derived from the leaves of <code>p</code>'s proof tree.
     */
    public String createTestForProof(Proof p, SetOfProgramMethod pms){
	return createTestForNodes(p.root().leavesIterator(), pms);
    }

    private ModelGenerator getModelGenerator(ExecutionTraceModel tr, Node n){
	return new ModelGenerator(serv, uc, tr.getLastTraceElement().node(),
				  tr.toString(),n);
    }
    

}
