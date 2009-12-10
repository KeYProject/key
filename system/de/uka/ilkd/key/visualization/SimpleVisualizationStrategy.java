// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualization;

import java.util.*;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.notification.events.GeneralFailureEvent;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.statement.BranchStatement;
import de.uka.ilkd.key.java.statement.LoopStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.JavaASTWalker;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.AbstractSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProgVarReplacer;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.rule.inst.ContextInstantiationEntry;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.metaconstruct.ResolveQuery;
import de.uka.ilkd.key.rule.metaconstruct.WhileInvRule;
import de.uka.ilkd.key.util.ExtList;

public class SimpleVisualizationStrategy implements VisualizationStrategy {

    static boolean DEBUG = false;
    /**Set this to true if you want to show a warning to the user. If this field
     * is true already, then don't show a warning to the user. In this way we
     * can reduce number of warning popups shown to the user. */
    private boolean warningOccured = false;

    /** used to extract branch labels
     */
    private static final String LOOP_INVARIANT_PROPOSAL_RULESET = "loop_invariant_proposal";


    private Services services;
    

    public SimpleVisualizationStrategy(){
    }
    
    public SimpleVisualizationStrategy(Services serv){
        this.services = serv;
    }
    
    
  
    private void computeAdditionalInformation(TraceElement te) {
        ContextTraceElement currentHe = firstSourceTraceElement(te);
        while (currentHe != TraceElement.END) {
            computeNumberUnwindings(currentHe);
            setLabel(currentHe);
            currentHe = currentHe.getNextExecuted();
        }
    }
        
    
    /** Computes how often the statement of cte was unwound.
     *  For details see minor thesis Proof Visualization.
     */
    private void computeNumberUnwindings(ContextTraceElement cte) {        
        if (cte.getParent() != TraceElement.PARENTROOT
                && cte.getParent().getSrcElement() instanceof LoopStatement) {
            final PositionInfo pos = cte.getSrcElement().getPositionInfo();
            final ContextTraceElement[] children = cte.getParent().getChildren();
            
            int n = 0;
            for (ContextTraceElement aChildren : children) {
                if (pos.equals(aChildren.getSrcElement().getPositionInfo())) {
                    n++;
                }
                if (aChildren == cte) {
                    break;
                }
            }
            cte.setNumberOfExecutions(n);
        
        } else {
            cte.setNumberOfExecutions(1);
        }
    }
    
    
    /** Computes the associations stepInto and parent of an execution trace model,
     *  that starts with the TraceElement te
     *  For details see minor thesis Proof Visualization, Chapter Building
     *  the Execution Trace Model
     */
   
    private void computeStepIntoAndParent(TraceElement te) {
        LinkedList stack = new LinkedList();
        stack.add(TraceElement.PARENTROOT);
        
        ContextTraceElement cte = firstSourceTraceElement(te);

        while (cte != TraceElement.END) {
            ParentContextTraceElement currentParent = 
                (ParentContextTraceElement) stack.getFirst();

            while (currentParent != TraceElement.PARENTROOT
                    && !contains(currentParent, cte)) {
                stack.removeFirst();                
                currentParent.setStepOver(cte);
                currentParent = (ParentContextTraceElement) stack.getFirst();
            }
            
            cte.setParent(currentParent);
            
            if (cte instanceof ParentContextTraceElement) {
                ((ParentContextTraceElement) cte).setStepOver(TraceElement.END);
                stack.addFirst(cte);
            }
            
            cte = cte.getNextExecuted();
        }
    }

    private boolean contains(ParentContextTraceElement pcte,
            ContextTraceElement cte) {
        
        final ProgramElement p1 = pcte.getProgram();
        final ProgramElement p2 = cte.getProgram();
        
        if (getMethodStackSize(p1) >= getMethodStackSize(p2)) {
            // per definition a statement does not contain itself
            if (pcte.getSrcElement().getPositionInfo().equals(
                    cte.getSrcElement().getPositionInfo())) {
                return false;
            }

            final StatementByPositionWalker walker = 
                new StatementByPositionWalker(
                        (ProgramElement) pcte.getSrcElement(), cte.getSrcElement()
                        .getPositionInfo());
            walker.start();

            return walker.getResult() != null;          
        }
        
        return true;
    }
    
    
    /** @return the number of Java blocks in the term t */
   
    private int countJavaBlocks(Term t) {
        int p = 0;
        // mbender
        // 'if (!t.javaBlock().isEmpty())' had to be switched back as it behaves
        // differently than
        // 'if (t.javaBlock() != JavaBlock.EMPTY_JAVABLOCK)'
        // That is if a JavaBlock contains an empty StatementBlock
        // 't.javaBlock() != JavaBlock.EMPTY_JAVABLOCK' is true but
        // '!t.javaBlock().isEmpty()' is false
        if (t.javaBlock() != JavaBlock.EMPTY_JAVABLOCK) {
            p++;
        }
        for (int i = 0; i < t.arity(); i++) {
            p = p + countJavaBlocks(t.sub(i));
        }
        return p;
    }


    /**
     * @param t term
     * @param inst instantions
     * @return the number of java blocks in the term t instatiated with inst
     */
    
    private int countJavaBlocksWithSV(Term  t, SVInstantiations inst){
        return countJavaBlocks(syntacticalReplace(t, services, inst));
    }

    /** creates the visualization model for a node by 
     * extracting the execution traces and building the
     * execution trace models
     */
    public VisualizationModel createVisualizationModel(Node node){
	return createVisualizationModel(node, new HashSet(), false);
    }
 
    /** creates the visualization model for a node by 
     * extracting the execution traces and building the
     * execution trace models
     */  
    public VisualizationModel createVisualizationModel(Node node, 
						       HashSet ignoreNodes,
						       boolean ignoreAntec) {
        Node currentNode = node;
        LinkedList executionTraceModelsList = new LinkedList();
	boolean jbInLastNode = false;

        // traces of the modalities in Node node
        if (getJavaBlocks(currentNode.sequent(), ignoreAntec).length>0){
            Occ[] javaBlocks = getJavaBlocks(currentNode.sequent(), ignoreAntec);
	    jbInLastNode = true;
            for (Occ javaBlock : javaBlocks) {
                ExecutionTraceModel etm =
                        getExecutionTraceModel(currentNode, javaBlock, ExecutionTraceModel.TYPE1);
                if (etm != null) {
                    executionTraceModelsList.add(etm);
                }
            }
        }
        // traces of modalities that ended "on the way" to Node node
        while (!currentNode.root() && !ignoreNodes.contains(currentNode)) {
            final LinkedList types = new LinkedList();
            final Occ[] ends = getTraceEnds(currentNode, types);
            for(int i = 0; i<ends.length; i++){
                print("Node "+currentNode.parent().serialNr()+"  ", ends[i]);
                final ExecutionTraceModel etm = 
                    getExecutionTraceModel(currentNode.parent(), ends[i],
                            (Integer)types.get(i));
		
                if (etm != null) {
		    etm.setTerminated(!jbInLastNode);                
		    executionTraceModelsList.add(etm);
                }
            }            
	    ignoreNodes.add(currentNode);
            currentNode = currentNode.parent();
       }
        final ExecutionTraceModel[] exTraceModels = 
            removeRedundandTraces((ExecutionTraceModel[])executionTraceModelsList.
                    toArray(new ExecutionTraceModel[executionTraceModelsList.size()]));
        printTraces(exTraceModels);
        
        return new VisualizationModel(node, exTraceModels);
    }
    
    /**
     * Computes the execution trace for the Java block occurrence occ in the
     * sequent of Node n
     */

    protected ExecutionTraceModel extractExecutionTrace(Node node, Occ occ,
            Integer type) {              
        TraceElement firstTraceElement = null;
        TraceElement lastTraceElement = TraceElement.END;        
        TraceElement lastSource = null;
        ContextTraceElement lastExecuted = TraceElement.END;
        
        print("------------- Creating Trace ");
        print("");
        
        TraceElement te;
        long rating = 0;
        
        Node currentNode = node;
        Occ currentJB    = occ;
        while (!currentNode.root()) {

            Occ result = new Occ(false, -1, -1);
            boolean inTrace = occInParent(currentNode, currentJB, result);
            currentJB = result;

            if (result.cfm == -1) {
                break;
            }
            currentNode = currentNode.parent();
            print("--");
            if (inTrace) {
                print("ACTIVE STATEMENT IN EXECUTION TRACE");
                final PosTacletApp pta = (PosTacletApp) currentNode.getAppliedRuleApp();                
                final ContextInstantiationEntry cie = 
                    pta.instantiations().getContextInstantiation();
                final SourceElement actStatement = getActStatement(currentNode);
                if (isContextStatement(actStatement)) {
                    rating++;
                    if (!isParentContextTE(actStatement)) {
                        te = new ContextTraceElement(actStatement, currentNode,
                                lastTraceElement, lastExecuted,
                                getExecutionContext(cie.contextProgram()));
                    } else {
                        te = new ParentContextTraceElement(actStatement,
                                currentNode, lastTraceElement, lastExecuted,
                                null, getExecutionContext(cie.contextProgram()));
                    }
                    // sets contextStatement
                    final MethodFrame frame = getMethodFrame(cie.contextProgram());
                    
                    if (frame != null && frame.getProgramMethod() != null) {
                        final StatementBlock methodBody = 
                            frame.getProgramMethod().getBody();                    
                        if (methodBody != null) {
                            StatementByPositionWalker w = new StatementByPositionWalker(
                                    methodBody, actStatement.getPositionInfo());
                            w.start();
                            if (w.getResult() != null) {
                                ((ContextTraceElement) te).
                                    setContextStatement(w.getResult());
                            }
                        }
                    }
                    
                    if (lastSource == null) {
                        lastSource = te;
                    }
                } else {
                    te = new TraceElement(actStatement, currentNode,
                            lastTraceElement, lastExecuted,
                            getExecutionContext(cie.contextProgram()));
                }
                if (firstTraceElement == null) {
                    firstTraceElement = te;
                }

                lastTraceElement = te;

                if (te instanceof ContextTraceElement) {
                    lastExecuted = (ContextTraceElement) te;
                }
            }
        }

        if (lastTraceElement != TraceElement.END) {
            return new ExecutionTraceModel(lastTraceElement, firstTraceElement,
                    (ContextTraceElement) lastSource, rating, currentNode,
                    node, type);
        }
        return null;
    }
    
    
    
    /**
     * @param ant
     *            determines if t occures in the antecedent or succedent in a
     *            formula
     * @param cfm position of <tt>t</tt>'s enclosing constrained formula  
     * 
     * @param t
     *            the term
     * @param pos
     *            offset that is added to the occurrences, needed for recursion
     * @return a list containing the occurrences of the java blocks in the term   
     */
    protected LinkedList findJavaBlocks(boolean ant, int cfm, Term t, int pos) {
        LinkedList ll = new LinkedList();
        int p = pos;
        if (!t.javaBlock().isEmpty()) {
            /*Occ objects additionally store the term with the javablock
             * that shall be traced. This information is important for the
             * implementation of extractExecutionTrace in class
             * VisualizationStrategyForTesting.
             */
            ll.add(new Occ(ant,cfm,p, t));
            p++;        
        }
        
        for (int i = 0; i < t.arity(); i++) {
            final LinkedList ll2 = findJavaBlocks(ant, cfm, t.sub(i), p);            
            p += ll2.size();            
            ll.addAll(ll2);
        }
        
        return ll;
    }

    
    private ContextTraceElement firstSourceTraceElement(TraceElement te) {
        if (te instanceof ContextTraceElement) {
            return (ContextTraceElement) te;
        } else {
            return te.getNextExecuted();
        }
    }


    protected SourceElement getActStatement(Node n) {
        SourceElement statement = n.getNodeInfo().getActiveStatement();
        while ((statement instanceof ProgramPrefix)||
                statement instanceof ProgramElementName) {
            if (statement == statement.getFirstElement()) {
                break;
            }
            statement = statement.getFirstElement();
        }
        return statement;
    }
      
    protected IExecutionContext getExecutionContext(SourceElement cp) {
        MethodFrame frame = getMethodFrame(cp);
        if (frame != null) {
            return frame.getExecutionContext();
        }
        return null;
    }
    
    private ExecutionTraceModel getExecutionTraceModel(Node node,
            Occ javaBlock,Integer type) {         
        print("-------------------------------");
        print("Extracting Execution Trace Model for Node "+node.serialNr()
                +" and ", javaBlock);

        final ExecutionTraceModel trace = extractExecutionTrace(node, javaBlock,type);
        if (trace == null) {
            return null;
        }

        computeStepIntoAndParent(trace.getFirstTraceElement());
        computeAdditionalInformation(trace.getFirstTraceElement());

        return trace;
    }



    /**
     * @param n Node
     * @return the goal template that yields to node n
     */
    
    private TacletGoalTemplate getGoalTemplate(Node n){
        final Node parent = n.parent();                
        
        final int nodeIndex = parent == null ?  -1 : parent.getChildNr(n);
        
        if(nodeIndex != -1) {            
            // if parent is null then nodeIndex has been set to -1 and 
            // this branch is not entered
            if (parent.getAppliedRuleApp() instanceof TacletApp) {
                final ImmutableList<TacletGoalTemplate> l = 
                    ((TacletApp) parent.getAppliedRuleApp()).taclet().goalTemplates();
                final TacletGoalTemplate[] gt = l.toArray(new TacletGoalTemplate[l.size()]);
                if (gt == null || gt.length == 0) {
                    return null;
                }
                return gt[gt.length-nodeIndex-1];
            }
        }
        print("Proof Visualization WARNING: " +
                        "Could not find goal template that yields to sequent of node ", 
                        n.serialNr());
        return null;
    }
   
    /** @return an array containing the occurrences of the Java 
     * blocks in the sequent
     */
    private Occ[] getJavaBlocks(Sequent sequent, boolean ignoreAntec) {
        LinkedList list = new LinkedList();
        
        final Iterator<ConstrainedFormula> iterator = sequent.succedent().iterator();        
        for (int i = 0; iterator.hasNext(); i++) {            
            list.addAll(findJavaBlocks(false, i , iterator.next().formula(), 0));
        } 

        if (!ignoreAntec) {
            final Iterator<ConstrainedFormula> antec = sequent.antecedent().iterator();
            for (int i = 0; antec.hasNext(); i++) {
                list.addAll(findJavaBlocks(true, i, antec.next().formula(), 0));              
            }
        }
 
        return (Occ[]) list.toArray(new Occ[list.size()]);
    }

    
    /**
     * collects all occurrences of schema variables or program blocks
     * that occur in the given goal template in linear order
     * @see #getList(Term)
     * @param tgt the TacletGoalTemplate 
     * @return all occurrences of schema variables or program blocks
     * that occur in the given goal template in linear order
     */
    private ExtList getList(TacletGoalTemplate tgt){
        ExtList templateList = new ExtList();
               
        List<Sequent> sequents = new LinkedList<Sequent>();
        
        if (tgt instanceof RewriteTacletGoalTemplate) {           
            templateList.addAll(getList(((RewriteTacletGoalTemplate) tgt).replaceWith()));
        } else if (tgt instanceof AntecSuccTacletGoalTemplate) {
            sequents.add(((AntecSuccTacletGoalTemplate) tgt).replaceWith());        
        }
        
        assert tgt.sequent() != null : "Sequent should always be != null"; 
        
        sequents.add(tgt.sequent());

        for (Sequent seq : sequents) {
            for (final ConstrainedFormula cf : seq) {
                templateList.addAll(getList(cf.formula()));
            }
        }
        return templateList;
    }

    /**
     * returns all occurrences of schema variables or program blocks in the
     * given term <tt>t</tt> in linear order
     * 
     * @param t the term to be linearized 
     * @return a list of all schema variable and Java blocks that occur in t
     *         Example:    \< int i;\> sv
     *                     --> [int i;, sv]
     */        
    private ExtList getList(Term t){
        final Operator op = t.op();
        ExtList result = new ExtList();
        
        if (op instanceof Modality || op instanceof ModalOperatorSV) {
            result.add(t.javaBlock());
        }
        
        if (op instanceof SchemaVariable){
	    result.add(op);
        }
        
        for (int i = 0; i < t.arity(); i++) {
	    result.addAll(getList(t.sub(i)));
	}
        
        return result;
    }
    
    
    /**
     * returns the inner most method frame of the abstract syntax tree
     * <tt>context</tt> 
     * @param context the SourceElement 
     */
    protected MethodFrame getMethodFrame(SourceElement context) {
        SourceElement se = context;
        MethodFrame frame = null;
       
        if (se instanceof MethodFrame) {
            frame = (MethodFrame) se;
        }
        
        while (se != se.getFirstElement()) {
            se = se.getFirstElement();
            if (se instanceof MethodFrame) {
                frame = (MethodFrame) se;
            }
        }
        return frame;
    }
    
    
    /**
     * computes the depth of the method frame stack up to the first active
     * statement 
     */
    private int getMethodStackSize(SourceElement context) {
        SourceElement se = context;
        int size =0;
        if (se instanceof MethodFrame) {
            size++;
        }
        while (se != se.getFirstElement()) {
            se = se.getFirstElement();
            if (se instanceof MethodFrame) {
                size++;
            }
        }
        return size;
    }
        
    
    
    
    /**
     * formula whose index in the parent node of <tt>n</tt> is 
     * <tt>indexInParent</tt> was not added to sequent of node n and
     *  is not the result of replacing or rewriting a formula, 
     *  so it occurs in the parent node.     
     * @return the index of the formula in the parent node. 
     *         See minor thesis Proof Visualization for details.                  
     */    
    private int getIndexOfUnchangedFormula(Node n, boolean antec, 
            int indexInParent){
        
        Semisequent parentSemi, semi;
        
        if (antec) {
	    parentSemi = n.parent().sequent().antecedent();
	    semi = n.sequent().antecedent();
	} else {
	    parentSemi = n.parent().sequent().succedent();
	    semi = n.sequent().succedent();
	}
        
        if (indexInParent < 0 || indexInParent >= semi.size()) {            
            return -1;
        }
        return indexOf(rename(parentSemi, n.getRenamingTable()), 
                semi.get(indexInParent));
    }
    
    
    
    
    /** 
     * computes the occurrence of the formula in the sequent of node
     * <tt>n</tt>, which has been in the focus of the rule application 
     * performed at node <tt>n</tt>
     * @param n the Node 
     * @return the occurrence of the focus formula in the sequent of node n
     */
    
    private Occ getOccOfFind(Node n){
    	if (!(n.getAppliedRuleApp()instanceof PosTacletApp)) {
            return null;
	}
        final PosInOccurrence pio = n.getAppliedRuleApp().posInOccurrence();

        final Semisequent semisequent;

        if (pio.isInAntec()) {
	    semisequent = n.sequent().antecedent();
	} else {
	    semisequent = n.sequent().succedent();
	}

	final int formulaIndex = semisequent.indexOf(pio.constrainedFormula());
        final int jb = getSubformulaOccurrence(pio.constrainedFormula().formula(),
					       pio.posInTerm().iterator());

        return new Occ(pio.isInAntec(), formulaIndex, jb, pio.subTerm());
    }
    


    /**@param t
     * @param inst
     * @return the occurrence of the first Java block in the instantiation of 
     *          term t
     * @note gladisch: It is unclear if an occurrence according to Def 4.
     * or according to Def. 5 is returned (see Minor Thesis of Markus Baum).
     */
    private int getOccurrenceOfJavaBlock(Term t, SVInstantiations inst){       
        int p = 0;
        for (Object o : getList(t)) {
            final Object next = o;
            int jbs = 0;
            if (next instanceof SchemaVariable) {
                Object instantiation =
                        inst.getInstantiation((SchemaVariable) next);
                if (instantiation instanceof Term) {
                    jbs = countJavaBlocks((Term) instantiation);
                }
            } else {
                return p;
            }
            p += jbs;
        }
        
        return -1;
    }

    /**This method is a variant of method {@code getOccurrenceOfJavaBlock}.
     * The purpose of this method in the class is to compute the field{@code jbt}
     * of {@code Occ}.
     * @param t term with Schema Variables
     * @param inst Instantiation of the Schema Variables
     * @return Should return the first term with a JavaBlock because
     * it is analogously implemented to {@code getOccurrenceOfJavaBlock}.
     * @author gladisch
     */
    private Term getTermWithJavaBlock(Term t, SVInstantiations inst){
        int p = 0;
        for (Object o : getList(t)) {
            final Object next = o;
            int jbs = 0;
            if (next instanceof SchemaVariable) {
                Object instantiation =
                        inst.getInstantiation((SchemaVariable) next);
                if (instantiation instanceof Term) {
                    jbs = countJavaBlocks((Term) instantiation);
                }
            } else {
                Term subt = t;
                if (subt.javaBlock() == null && !warningOccured) {
                    warningOccured = true;
                    String tStr = t.toString();
                    tStr = tStr.length() > 160 ? tStr.substring(0, 160) + " ..." : tStr;
                    String subtStr = subt.toString();
                    subtStr = subtStr.length() > 160 ? subtStr.substring(0, 160) + " ..." : subtStr;
                    Main.getInstance().notify(new GeneralFailureEvent("Warning: SimpleVisualizationStrategy.getTermWithJavaBlock " +
                            "returns a term without a JavaBlock.\n Variable p=" + p + "\n Given term=" + subtStr));
                }
                return (Term) next;
            }
            p += jbs;
        }
        
        return null;
    }
  
    
    /**
     * determines the occurrence of schemavariable <code>svToFind</code> in 
     * the schematic term <code>t</code>.
     * The occurrence of schemavariable <code>svToFind</code> is here defined as 
     * the number of java blocks of the instantiated version of term <code>t</code>
     * before the first time <code>svToFind</code> occurs in 
     * <code>t</code> (linearized <code>t</code>).  
     * For example:
     * <code>
     *    #b = TRUE | <{.. #t #i; ...}>#post -> #fml | #svToFind = 3
     * </code>
     * has occurrence <code>1</coode> if the instantiations of 
     * <code>#b,#post,#fml</code> contain no java block.   
     *   
     * Assumption: no metaoperators in t
     * 
     * @param t the Term relative to which the occurrence of <code>svToFind</code>
     * (it is assumed that <code>t</code> does not contain a metaoperator) has to 
     * be determind
     * @param svToFind the SchemaVariable to look for
     * @param inst the SVInstantiations   
     * @return occurrence of <code>svToFind</code> in <code>t</code> 
     */        
    private int getOccurrenceOfSV(Term t, SchemaVariable svToFind,
            SVInstantiations inst) {       
        final Iterator it = getList(t).iterator();
        int p = 0;
        while (it.hasNext()) {
            final Object next = it.next();
            int jbs = 0;
            if (next instanceof SchemaVariable) {
                final SchemaVariable sv = (SchemaVariable) next;
                if (sv.equals(svToFind)) {
                    return p;
                } else {
                    Object instantiation = inst.getInstantiation(sv);
                    if (instantiation instanceof Term) {
                        jbs = countJavaBlocks((Term) instantiation);
                    }
                }
            } else {
                jbs = 1;
            }
            p += jbs;
        }
        return -1;
    }

    

    
    /**
     * 
     * computes the formula index <tt>idx</tt> in node <tt>n</tt>'s 
     * sequent for the formulas occuring in the given sequent being instantiated by 
     * the mapping used by the taclet application in <tt>n</tt>'s parent node.    
     * 
     * @param schemaSeq the Sequent to be instantiated, i.e. replacewith or add sequent
     *   in the goal template of the taclet applied at <tt>n.parent()</tt> 
     * @param n the Node where to look for the instantiated formulas
     * @param antec boolean value indicating if the antec or succedent of the sequent shall 
     * be instantiated
     * @param services the Services 
     * @return a hashmap that maps the position of replaced cfm given by the index to the template
     *          of the formula
     *          These are the formulas that build by the part replacewith(S) where S is a sequent
     */
  
    private HashMap getIndexedInstantiatedFormulas(Sequent schemaSeq, Node n,
            boolean antec, Services services){
        // index to schematic formula
        final HashMap index2cfm = new HashMap();
 
        final TacletApp tacletApp = (TacletApp)n.parent().getAppliedRuleApp();

        for (Object o : (antec ? schemaSeq.antecedent() : schemaSeq.succedent())) {
            final ConstrainedFormula cfm = (ConstrainedFormula) o;


            final ConstrainedFormula newCfm =
                    instantiateReplacement(cfm, tacletApp.matchConditions(),
                            services);

            int index = antec ? indexOf(n.sequent().antecedent(), newCfm) :
                    indexOf(n.sequent().succedent(), newCfm);

            if (index == -1) {
                print("Proof Visualization WARNING: CFM INST NOT FOUND: ", cfm);
                print("instantiated with ", newCfm);
            } else {
                index2cfm.put(new Integer(index), cfm);
            }
        }
        
        return index2cfm;
    
    }
    
    /**
     * determines the index of the constrained formula in the the antecedent
     *  (<code>antec == true</code>) or succedent (<code>antec == false</code>) of 
     *  <code>n</code> which is the result of the rewrite described by the goal template
     *   <code>gt</code> of a formula in <code>n.parent</code>  
     * @param gt the {@link RewriteTacletGoalTemplate} describing the rewrite
     * @param n the Node which resulting from an application of a taclet <code>gt</code> 
     * belongs to and where to look for the rewritten formula
     * @param antec a boolean indicating in which semisequent to look for
     * @param services the Services
     * @return the index of the reritten formula relative to the specified 
     * semisequent or <code>-1</code> if none has been found  
     */
    private int getIndexedInstantiatedRewrittenFormula(RewriteTacletGoalTemplate gt, 
            Node n, boolean antec, Services services) {
       
        final TacletApp tacletApp = ((TacletApp) n.parent().getAppliedRuleApp());
        final PosInOccurrence posOfFind = tacletApp.posInOccurrence();

        if (posOfFind.isInAntec() != antec) {
            print("nothing rewritten in the semisequent");
            return -1;
        }

        final MatchConditions matchCond = tacletApp.matchConditions();
        final PosInOccurrence flatPos = flatten(posOfFind, services);

        final Term term = flatPos.constrainedFormula().formula();
      
        final Term result = replace(term, gt.replaceWith(), 
                flatPos.posInTerm().iterator(), services, 
                matchCond.getInstantiations(), term.sort());              
        
        final Semisequent semi = antec ? n.sequent().antecedent() : 
            n.sequent().succedent();
       
        int index = indexOf(semi, 
                            new ConstrainedFormula(rename(result, 
                                                          n.getRenamingTable()), 
                                                          matchCond.getConstraint()));
        if (index == -1) {
            print("Proof Visualization WARNING: Replacewith not"
                    + " found in node ", n.serialNr());
        }
        return index;
    }
    
    
    /**
     * @param t term
     * @param it a path to subformula in the tree representation of t
     * @return the number of Java blocks that occur "on the left" of
     *         the subformula,that is given by it, in t 
     */
    
    private int getSubformulaOccurrence(Term t, IntIterator it){
        int result = 0;
        if (it.hasNext()) {
            if (!t.javaBlock().isEmpty()){
                result++;
            }
            
            int sub = it.next();
            for (int i = 0; i < sub; i++) {
                result += countJavaBlocks(t.sub(i));
            }
            result += getSubformulaOccurrence(t.sub(sub),it);
        }
        return result;
    }
    
    /** 
     * @param t a schematic term
     * @param occ an occurrence of a Java block in the instantiated term t 
     * @param inst the instantions
     * @return the occurrence of the Java block in the instantiation of a 
     *        schema variable in t or a modality
     *        or null if there is no such schema variable or modality
     */
    
    private OccInSchema getSVofOcc(Term  t, int occ, SVInstantiations inst){               
        final Operator op = t.op();
        if ( (op instanceof ModalOperatorSV) && (occ==0)) {
            // if t.javaBlock() is not a ContextStatementBlock, 
            // the tracing ends 
            if (isContextBlock(t.javaBlock())) {
                return new OccInSchema(t.javaBlock());
            } 
            return null;
        } else if ( op instanceof SchemaVariable && !(op instanceof ModalOperatorSV)) {
            return new OccInSchema((SchemaVariable)op, occ);
        } else if ((op instanceof Modality) && (occ==0)){
            // if t.javaBlock() is not a ContextStatementBlock, 
            // the tracing ends 
            if (isContextBlock(t.javaBlock())) {
                return new OccInSchema(t.javaBlock());
            }
            return null;
        } else {

            if (op instanceof Modality || op instanceof ModalOperatorSV){
                occ--;
            }

            // special handling for some metaoperators
            if (op instanceof WhileInvRule){
                if (occ==0) {
                    return new OccInSchema(t.javaBlock());
                } else if (occ==1) {
                    return null;
                } else if (occ<countJavaBlocksWithSV(t.sub(0),inst)+1) {
                    return new OccInSchema((SchemaVariable)t.sub(0).sub(0).op(),occ-2);
                } else {
                    if (!(t.sub(1).op() instanceof SchemaVariable)) {
                        // termination branch
                        return null;
                    }
                    return new OccInSchema((SchemaVariable)t.sub(1).op(),
                            occ-countJavaBlocksWithSV(t.sub(0),inst)-1);
                } 
            } else if (op instanceof ResolveQuery){
                // ResolveQuery only introduces new Java blocks
                return null;
            } else {
                for (int i = 0; i < t.arity(); i++) {
                    int blocks = countJavaBlocksWithSV(t.sub(i),inst);
                    if (blocks <= occ){
                        occ = occ-blocks;
                    } else {
                        OccInSchema result = getSVofOcc(t.sub(i),occ,inst);
                        if (result == null) {
                            return null;
                        } else {
                            if (result.isJavaBlock) {
                                return new OccInSchema(t.javaBlock());
                            } else {
                                return new OccInSchema(result.sv, result.occ);
                            }
                        }
                    }
                }              
            }
        }        
        print("Proof Visualization WARNING: Something went wrong in method getSVofOcc");
        return null;
    }
    
    
    /**
     * 
     * @param n a node with <code>parent != null</code>
     * @param types
     * @return the occurrence of all Java blocks that occure 
     *          in the sequent of the parent of n and not in 
     *          the sequent of n 
     */
    private Occ[] getTraceEnds(final Node n, LinkedList types) {
        LinkedList result = new LinkedList();
        final Node parent = n.parent();
        
        print("TraceEnds for Node " + n.serialNr() + " ----------");        
        if (parent.getAppliedRuleApp() instanceof TacletApp) {
            final TacletApp tacletApp = (TacletApp) parent.getAppliedRuleApp();
            if (tacletApp.taclet() instanceof FindTaclet) {
                final TacletGoalTemplate tgt = getGoalTemplate(n);               
                if (tgt == null) {
                    return new Occ[0];
                }               
                
                ExtList otherTgts = new ExtList();
                for (TacletGoalTemplate tacletGoalTemplate : tacletApp.taclet().goalTemplates()) {
                    final TacletGoalTemplate currentTgt = tacletGoalTemplate;
                    if (!currentTgt.equals(tgt)) {
                        otherTgts.addAll(getList(currentTgt));
                    }
                }                
               
                final Term findTerm = ((FindTaclet)tacletApp.taclet()).find();               
                
                ExtList templateList = getList(tgt); 
                ExtList findList = removeCommonSVsOrPrograms(getList(findTerm), 
                        templateList);                                              
                
                final Occ occOfFind = getOccOfFind(parent);
                
                final SVInstantiations inst = tacletApp.instantiations();
                for (Object aFindList : findList) {
                    Object current = aFindList;
                    if (current instanceof SchemaVariable) {
                        SchemaVariable sv = (SchemaVariable) current;
                        int occOfSV = getOccurrenceOfSV(findTerm, sv, inst);
                        if (occOfSV > -1
                                && inst.getInstantiation(sv) instanceof Term) {

                            int jbCount =
                                    countJavaBlocks((Term) inst.getInstantiation(sv));

                            final Integer type = otherTgts.contains(sv) ?
                                    ExecutionTraceModel.TYPE2
                                    : ExecutionTraceModel.TYPE1;

                            for (int i = 0; i < jbCount; i++) {
                                Occ newOcc = new Occ(occOfFind.ant,
                                        occOfFind.cfm, occOfFind.jb + occOfSV + i,
                                        (Term) inst.getInstantiation(sv));  //chrisg                              
                                result.add(newOcc);
                                types.add(type);
                            }
                        }
                    } else {
                        result.add(occOfFind.copy());
                        types.add(ExecutionTraceModel.TYPE1);
                    }
                    print("ends:  ", findList);
                }
            }
        }       
        return (Occ[])result.toArray(new Occ[result.size()]);
    }

    /**
     * removes SVs or programs (TODO: is the implementation correct 
     * (only remove context blocks?)) from find list
     * Attention: the list returned == <tt>findList</tt> (works destructively on 
     * <tt>findList</tt>) 
     * @param findList the List from which elements are removed
     * @param templateList the List where to look for common elements
     * @return returns findList (attention same object as first parameter)
     */
    private ExtList removeCommonSVsOrPrograms(ExtList findList, ExtList templateList) {
        final JavaBlock first = (JavaBlock) findList.get(JavaBlock.class);

        for (Object aTemplateList : templateList) {
            Object current = aTemplateList;
            print(current);
            if (current instanceof SchemaVariable) {
                if (findList.contains(current)) {
                    findList.remove(current);
                }
            } else {
                JavaBlock jb = (JavaBlock) current;
                if ((first != null) && isContextBlock(jb)
                        && isContextBlock(first)) {
                    findList.remove(first);
                }
            }
        }
        return findList;
    }
    
    

    /**
     * @param semi  semi
     * @param toFind toFind that should be found in semi
     * @return index of the formula toFind in the semisequent semi or -1 if it
     *         does not exist. Equality is checked modulu renamings
     */
 
    private int indexOf(Semisequent semi, ConstrainedFormula toFind){
        final Iterator<ConstrainedFormula> iterator = semi.iterator();        
        int i=0;
        while (iterator.hasNext()) {
            final ConstrainedFormula cfm = iterator.next();
            try{
                if (cfm.formula().equalsModRenaming(toFind.formula())){
                    return i;
                }
                i++;
            }catch(Exception e){           
                return i;
            }
        }
        return -1;
    }

    private ConstrainedFormula 
        instantiateReplacement(ConstrainedFormula schemaFormula, 
                MatchConditions matchCond, Services services) {        
        final SVInstantiations svInst = matchCond.getInstantiations();
        
        Term replaced = syntacticalReplace(schemaFormula.formula(),
                services, svInst);

        if (!svInst.getUpdateContext().isEmpty()) {                 
            replaced = TermFactory.DEFAULT.createUpdateTerm(svInst
                    .getUpdateContext(), replaced);
        }

        return new ConstrainedFormula(replaced, matchCond.getConstraint());
    }
    
    private boolean isContextBlock(JavaBlock jb){
        return jb.program() instanceof ContextStatementBlock;
    }
     
    protected boolean isContextStatement(SourceElement s) {
        if (s != null) {
            final PositionInfo pos = s.getPositionInfo();
            return pos != null && pos.getFileName() != null
                    && pos != PositionInfo.UNDEFINED
                    && pos.getStartPosition() != null
                    && pos.getStartPosition().getLine() > -1;
        }
        return false;
    }

    /**
     * @param se a SourceElement
     * @return true iff se is associated with a ParentContextTraceElment.
     *         This means that se contains statements or a method invokation
     */    
    protected boolean isParentContextTE(SourceElement se) {
        if (se instanceof MethodReference 
                || se instanceof LoopStatement
                || se instanceof BranchStatement) {
            return true;
        } 
        
        boolean isParentContextTE = false;
        if (se instanceof ProgramElement) {
            final MethodReferenceWalker tw = 
                new MethodReferenceWalker((ProgramElement) se);
            tw.start();
            isParentContextTE = (tw.containsMethodRef().size()>0);
        } 
        
        return isParentContextTE;
    }


    /**
     * For details see minor thesis about Proof Visualization:
     * Section Extracting Execution Traces.
     * This method corresponds to the methods OccIn, codeTransformation
     * and formulaInvolved in the minor thesis.
     * 
     * @param n a node
     * @param occ a Java block occurrence in the sequent of Node n
     * @param result the occurrence of occ in the sequent of the parent node, that
     *        is computed by this method
     * @return a boolean that is true iff the java block was changed
     *         and the occurrence result of the Java block in the parent node 
     */
    
    protected boolean occInParent(Node n, Occ occ, Occ result){
      
        print("Node "+n.serialNr()+ "  Occ: ", occ);
        final Node parent = n.parent();          
        final RuleApp appliedRuleApp = parent.getAppliedRuleApp();
        
        if (appliedRuleApp instanceof BuiltInRuleApp) {
            return indexAfterBuiltInRuleApplication(n, occ, result);
        } 
        
        final TacletGoalTemplate tgt = getGoalTemplate(n);
        
        if (tgt == null){
            print("ProofVisualization WARNING: No goal template found");
            result.copy(occ);
            return false;
        }                
        print("Goal Template: ", tgt);
        
        HashMap index2cfmAnt =
            getIndexedInstantiatedFormulas(tgt.sequent(), n, true, services);
        HashMap index2cfmSuc = 
            getIndexedInstantiatedFormulas(tgt.sequent(), n, false, services);
        
        print("Added Formulas:   Ant: " , index2cfmAnt.keySet());
        print("  Suc:", index2cfmSuc.keySet());    

        final Integer cfmIndexKey = new Integer(occ.cfm);
        
        if (!(appliedRuleApp instanceof PosTacletApp)){
            print("NoPosTacletApp");
            if ((index2cfmAnt.containsKey(cfmIndexKey)&& occ.ant)||
                        (index2cfmSuc.containsKey(cfmIndexKey)&&!occ.ant)){
                // occ was added, tracing ends since there is no find part
                result.set(false, -1, -1);
                return false;
            }
            // otherwise occ occurres in parent
            result.set(occ.ant, 
                    getIndexOfUnchangedFormula(n, occ.ant, occ.cfm), occ.jb, occ.jbt);           
            print("Occ was not changed or added");
            return false;
        }

        final PosTacletApp pta = (PosTacletApp) appliedRuleApp;       
        final Taclet taclet = pta.taclet();
        
        assert cfmIndexKey.intValue() == occ.cfm;        
        if (taclet instanceof RewriteTaclet) {
            return indexAfterRewriteTacletApplication(occ, 
                    result, tgt, n, pta, index2cfmAnt, index2cfmSuc);
        } else if (taclet instanceof AntecTaclet || taclet instanceof SuccTaclet) {
            // Case 2.2
            return indexAfterAntecSuccTacletapplication(occ, result, tgt, n,
                    pta, index2cfmAnt, index2cfmSuc);
        }
        
        result.set(occ.ant, occ.cfm, occ.jb, occ.jbt);       
        return false;
  }

    /**
     */
    private boolean indexAfterBuiltInRuleApplication(Node n, Occ occ, Occ result) {
        final Node parent = n.parent();
        final BuiltInRuleApp bira = 
            (BuiltInRuleApp) parent.getAppliedRuleApp();
        boolean ant = bira.posInOccurrence().isInAntec();
        int indexOfUpSimpl = parent.sequent().formulaNumberInSequent(ant, 
                bira.posInOccurrence().constrainedFormula());
        if (!ant) {
            indexOfUpSimpl = indexOfUpSimpl
                    - parent.sequent().antecedent().size();
        }
        indexOfUpSimpl--;
        int newCfm = getIndexOfUnchangedFormula(n, occ.ant, occ.cfm);
        print("Index Of simplified Formula: ", indexOfUpSimpl);

        /*
         * if occ does not occure in the sequent of the parent it was
         * changed by an update simplification rule
         */
        if (newCfm == -1) {
            newCfm = indexOfUpSimpl;
        }
        result.set(occ.ant, newCfm, occ.jb, occ.jbt);
        return false;
    }


    /**
     * return occInParentOfRewriteTaclet(occOfFind, occ, result, tgt, 
                    n, pta, inst, cfmIndexKey, index2cfmAnt, index2cfmSuc);
     */
    private boolean indexAfterAntecSuccTacletapplication(Occ occ, 
            Occ result, TacletGoalTemplate tgt, Node n, 
            PosTacletApp pta, HashMap index2cfmAnt, HashMap index2cfmSuc) {
        
        final Occ occOfFind = getOccOfFind(n.parent());
        print("Occ of Find ", occOfFind);
        
        final FindTaclet taclet = (FindTaclet) pta.taclet();
       
        if ((tgt instanceof AntecSuccTacletGoalTemplate)) {
            
            final HashMap indexToReplaceAnt = getIndexedInstantiatedFormulas(
                    ((AntecSuccTacletGoalTemplate) tgt).replaceWith(), 
                    n, true, services);
            
            final HashMap indexToReplaceSucc = getIndexedInstantiatedFormulas(
                    ((AntecSuccTacletGoalTemplate) tgt).replaceWith(), 
                    n, false, services);

            print("Repl:   Ant:", indexToReplaceAnt.keySet());
            print("Suc:", indexToReplaceSucc.keySet());

            index2cfmAnt.putAll(indexToReplaceAnt);
            index2cfmSuc.putAll(indexToReplaceSucc);
        }

        final Integer cfmIndexKey = new Integer(occ.cfm);
        if ((index2cfmAnt.containsKey(cfmIndexKey) && occ.ant)
                || (index2cfmSuc.containsKey(cfmIndexKey) && !occ.ant)) {
            // pos.cfm was added or replaced
            print("pos was replaced or added");                                
            
            final Term findTerm = taclet.find();
            final ConstrainedFormula newCfm;

            if (occ.ant) {
                newCfm = (ConstrainedFormula) index2cfmAnt.get(cfmIndexKey);
            } else {
                newCfm = (ConstrainedFormula) index2cfmSuc.get(cfmIndexKey);
            }
            
            print("changed Formula template", newCfm);
            final SVInstantiations inst = pta.matchConditions().getInstantiations();
            final OccInSchema occInSV = getSVofOcc(newCfm.formula(), occ.jb,
                    inst);
            
            print("Occ in SV", occInSV);

            int occOfSV = -1;

            if (occInSV != null) {
                print("Occurrence in Schema Variable: " + occInSV.sv
                        + "   occ ", occInSV.occ);
                if (occInSV.isJavaBlock) {
		    // author: mbender
		    // Bugfix implemented by Christoph Gladisch caused an
		    // exception (Cannot cast JavaBlock to Term) if the proof
		    // tree contained the application of the invariant rule
                    
		    // result.set(occOfFind.ant, occOfFind.cfm,
		    // getOccurrenceOfJavaBlock(findTerm, inst),
		    // getTermWithJavaBlock(findTerm, inst));

		    // This looks like a solution for the above mentioned bug,
		    // but due to the complexity code we are not
		    // sure if findTerm really equals the javablock-term in all
		    // cases
                    
		    result.set(occOfFind.ant, occOfFind.cfm,
			    getOccurrenceOfJavaBlock(findTerm, inst),
			    findTerm);
                    return true;
                } else {
                    occOfSV = getOccurrenceOfSV(findTerm, occInSV.sv, inst);
                }
            }
            
            print("" + occOfSV);

            if (occOfSV == -1) {
                // the schema variable does not occure in the find
                // part, so an execution trace starts at this node
                result.set(occOfFind.ant, -1, -1);                
                return false;
            }
            
            print("Occurrence of sv in find ", occOfSV);
            result.set(occOfFind.ant, occOfFind.cfm, occOfSV + occInSV.occ, occOfFind.jbt);            
            return false;
        } else {
            // Case 1
            print("occ was not replaced or added");
            int newCfm = getIndexOfUnchangedFormula(n, occ.ant, occ.cfm);
            print("newCfm ", newCfm);

            if (newCfm == -1) {
                newCfm = occ.cfm;
            }

            result.set(occ.ant, newCfm, occ.jb, occ.jbt);            
            return false;
        }
    }
    
    
    
    /**
     */
    private boolean occInParentHelper(Occ occOfFind, Term find, Term newTerm,
            int javaBlockOcc, Occ result, SVInstantiations inst) {

        final OccInSchema pisv = getSVofOcc(newTerm, javaBlockOcc, inst);
        int occOfSV = -1;

        if (pisv != null) {
            print("SchemaVariable of Occ: " + pisv.sv + "  occInSV ", pisv.occ);
            result.set(occOfFind.ant, occOfFind.cfm, result.jb);
         
            if (pisv.isJavaBlock) {
                occOfSV = getOccurrenceOfJavaBlock(find, inst);
            } else {
                occOfSV = getOccurrenceOfSV(find, pisv.sv, inst);
            }
        }

        print("occOfSV in find part ", occOfSV);

        if (occOfSV == -1) {
            // the schema variable does not occure in the find
            // part, so an execution trace starts at this node
            result.cfm = -1;
            result.jb = -1;
            return false;
        }

        result.jb = occOfFind.jb + occOfSV + pisv.occ;
        return pisv.isJavaBlock;
    }

    /**
     * returns the index of the rewritten formula
     */
    private int getIndexOfRewrittenFormula(TacletGoalTemplate tgt, Node n, 
					   Occ occOfFind, Occ occ, 
					   Services services) {
	int indexOfRewrite = -1;
	if (tgt instanceof RewriteTacletGoalTemplate){
	    final RewriteTacletGoalTemplate rwGoalTemplate  = 
		(RewriteTacletGoalTemplate)tgt;
	    
	    indexOfRewrite = getIndexedInstantiatedRewrittenFormula(rwGoalTemplate, n, occ.ant, services);
	    print("Rewritten Formula: ", indexOfRewrite);	   
	    // occ.cfm was not added
	    // occ.cfm  was replaced?	   
	   // TODO HACK
	    if (indexOfRewrite==-1) {
		indexOfRewrite = occOfFind.cfm;
	    }
	} 
	
	return indexOfRewrite;
    }
            
    /**
     */
    private boolean indexAfterRewriteTacletApplication(Occ occ, Occ result, 
            TacletGoalTemplate tgt, Node n, 
            PosTacletApp pta, HashMap index2cfmAnt, HashMap index2cfmSuc) {
        //Case 2.1
        final Occ occOfFind = getOccOfFind(n.parent());
        print("Occ of Find ", occOfFind);
       
        final RewriteTaclet rwTaclet = (RewriteTaclet)pta.taclet();
        final SVInstantiations inst = pta.matchConditions().getInstantiations();
        final Term findTerm = rwTaclet.find();
        
        final Integer cfmIndexKey = new Integer(occ.cfm);
        if ((index2cfmAnt.containsKey(cfmIndexKey) && occ.ant) ||
                (index2cfmSuc.containsKey(cfmIndexKey) && !occ.ant)){               
            // Case 2.1.2: occ.cfm was added
            print("occ was added");
            ConstrainedFormula addCfm;
            if (occ.ant) { 
                addCfm = (ConstrainedFormula) 
                index2cfmAnt.get(cfmIndexKey); 
            } else {
                addCfm  = (ConstrainedFormula) 
                index2cfmSuc.get(cfmIndexKey);
            }                  
            return occInParentHelper(occOfFind, findTerm, 
                    addCfm.formula(), occ.jb, result, inst);
        } else {
            final int indexOfRewrite = getIndexOfRewrittenFormula(tgt, n, occOfFind, 
							    occ, services);
            // check for replacewith part                 
            if ((indexOfRewrite == occ.cfm) && (occ.ant == occOfFind.ant)){
                print("pos.cfm was replaced");                
                int javaBlocksInFind = countJavaBlocks(pta.posInOccurrence().subTerm());
                //Case 2.1.1
                if (occ.jb >= occOfFind.jb){
                    final Term replaceTerm = ((RewriteTacletGoalTemplate) tgt).replaceWith();
                    int javaBlocksInRepl = countJavaBlocksWithSV(replaceTerm,inst);
                    
                    print("Blocks in Repl: ", javaBlocksInRepl);
                    print("Blocks in Find: ", javaBlocksInFind);
                    
                    // Case 2.1.1.3: occ "after" replace
                    if (occ.jb >= occOfFind.jb+javaBlocksInRepl) {
                        print("occ after replace");
                        result.set(occOfFind.ant, occOfFind.cfm, 
                                occ.jb+(javaBlocksInFind-javaBlocksInRepl),occOfFind.jbt);                       
                        return false;
                    }
                    
                    // Case 2.1.1.2: occ "in" replace
                    print("Occ is result of rewriting a subformula");
                    
                    return occInParentHelper(occOfFind, findTerm, 
                            replaceTerm, occ.jb - occOfFind.jb, 
                            result, inst);
                } else {
                    // Case 2.1.1.1: occ "before" replace
                    print("Occ before replace occ");
                    
                    result.copy(occ);                   
                    return false; 
                }            
            } else {
                // Case 1
                result.set(occ.ant, 
                        getIndexOfUnchangedFormula(n, occ.ant, occ.cfm), occ.jb, occ.jbt);
                print("Occ was not changed or added");
                return false;
            }
            
        }
    }
    
    protected void  print(Object o, Object o2){
        if (DEBUG) {
            System.out.println(o+""+o2);
        }
    }   
    
    protected void  print(Object o, int i){
        if (DEBUG) {
            System.out.println(o+""+i);
        }
    }  

    protected void  print(Object o){
        if (DEBUG) {
            System.out.println(o);
        }
    }    

    /**
     * prints the extracted execution trace models    
     */
    private void printTraces(ExecutionTraceModel[] exTraceModels) {        
        if (DEBUG) {
            print("Number of traces ", exTraceModels.length);
            for (ExecutionTraceModel exTraceModel : exTraceModels) {
                print("Trace Start ", exTraceModel.getFirstNode().serialNr());
                print("      End ", exTraceModel.getLastNode().serialNr());
                print("Type ", exTraceModel.getType());
                TraceElement te = exTraceModel.getFirstTraceElement();
                while (te != TraceElement.END) {
                    print("", te.node().serialNr());
                    te = te.getNextInProof();
                }
            }
        }
    }

    
    
    /**
     * 
     * @param t1 ExecutionTraceModel
     * @param t2 ExecutionTraceModel
     * @return true iff t1 is a part of t2
     * 
     */
    
    private boolean redundant(ExecutionTraceModel t1, ExecutionTraceModel t2){
        if (t1.getLastTraceElement().serialNr()>
            t2.getLastTraceElement().serialNr()) {
            return false;
        }
        TraceElement te1 = t1.getFirstTraceElement();
        TraceElement te2 = t2.getFirstTraceElement();
        while (te1!=TraceElement.END){
            if(te1.serialNr()!=te2.serialNr()){
                return false;
            }
            te2 = te2.nextInProof ;
            te1 = te1.nextInProof ;
        }
        return true;
    }
    
    
    /**
     * @param traces
     * @return removes every trace that is  a  part of another
     */
    
    private ExecutionTraceModel[] removeRedundandTraces(ExecutionTraceModel[] traces){
        LinkedList result = new LinkedList();
        for(int i=0;i<traces.length;i++){
            if (traces[i]==null) {
                continue;
            }
            boolean redundant=false;
            for(int j=0;j<traces.length;j++){
                if (j!=i && (traces[j]!=null)&&
                    redundant(traces[i],traces[j])) {
                    redundant = true;
                }
            }
            if (!redundant) {
		result.add(traces[i]);
            } else { 
                traces[i]=null;
	    }
        }
        ExecutionTraceModel[] exTraceModels= new ExecutionTraceModel[result.size()];
        result.toArray(exTraceModels);       
        return exTraceModels;
    }



    /** renames a sequent 
     * 
     * @param semi
     * @param renamings a list of HashMaps, that contains the renamings
     * @return a sequent that is the result of renaming variables in the order
     *          the renamings appear in the list;
     */
    private Semisequent rename(Semisequent semi, ImmutableList<RenamingTable> renamings){
        if (renamings!=null){
            for (RenamingTable renaming : renamings) {
                RenamingTable rt = renaming;
                HashMap hm = rt.getHashMap();
                ProgVarReplacer pvr = new ProgVarReplacer(hm, services);
                SemisequentChangeInfo sci = pvr.replace(semi);
                semi = sci.semisequent();
            }
        }
        return semi;
    }

    
    
    private Term rename(Term formula,ImmutableList<RenamingTable> renamings){
        if (renamings!=null){
            for (RenamingTable renaming : renamings) {
                RenamingTable rt = renaming;
                HashMap hm = rt.getHashMap();
                ProgVarReplacer pvr = new ProgVarReplacer(hm, services);
                formula = pvr.replace(formula);
            }
        }
        return formula;
    }



    /**
     * @param ste a ContextTraceElement
     */
    
    private void setLabel(ContextTraceElement ste) {
        if (tacletWithLabel(ste.node(), LOOP_INVARIANT_PROPOSAL_RULESET)) {
            final TraceElement next = ste.getNextInProof();
            if (next != TraceElement.END) {
		final Iterator<Node> it = ste.node().childrenIterator();
		while (it.hasNext()) {
		    final Node subTree = it.next();
		    if (subTree.find(next.node())) {
			ste.setLabel(subTree.getNodeInfo().getBranchLabel());
			break;
		    }
		}
	    }
        }
    }

    
    private boolean tacletWithLabel(Node n, String ruleSet) {
        if (n.getAppliedRuleApp() instanceof TacletApp) {
            final Name ruleSetName = new Name(ruleSet); 
            final Iterator<RuleSet> rs =  ((TacletApp) n.getAppliedRuleApp()).taclet().ruleSets();
    
            while (rs.hasNext()) {
                if (rs.next().name().equals(ruleSetName)) {
                    return true;
                }
            }
        }
        return false;
    }


    /** The following methods are needed to replay the taclet application
     * in order to figure out which formulas are added or rewritten.
     * Copied from Taclet.java
     * TODO remove these methods 
     *  
     **/    
    private Term syntacticalReplace(Term term, Services services,
            SVInstantiations svInst) {
        SyntacticalReplaceVisitor srVisitor = new SyntacticalReplaceVisitor(
                services, svInst);
        term.execPostOrder(srVisitor);

        return srVisitor.getTerm();
    }
    
    
    /**
     * Check if p_pos contains an explicit metavariable instantiation,
     * and creates in this case a new simple term by replacing the
     * metavariable with the instantiation
     */
    private PosInOccurrence flatten ( PosInOccurrence p_pos,
                                      Services        p_services) {
        if ( p_pos.termBelowMetavariable () != null ) {
            Term flatTerm = replace ( p_pos.constrainedFormula ().formula (),
                                      p_pos.termBelowMetavariable (),
                                      p_pos.posInTerm ().iterator (),
                                      p_services,
                                      SVInstantiations.EMPTY_SVINSTANTIATIONS,
                                      Sort.FORMULA);

            PosInOccurrence pos = new PosInOccurrence
                ( new ConstrainedFormula ( flatTerm,
                                           p_pos.constrainedFormula ().constraint () ),
                  p_pos.posInTerm (),
                  p_pos.isInAntec() );

            IntIterator it = p_pos.posInTermBelowMetavariable ().iterator ();
            while ( it.hasNext () ) {
                pos = pos.down ( it.next () );
            }

            return pos;
        }

        return p_pos;
    }
    
    /**
     * does the work for applyReplacewith (wraps recursion) 
     */
    private Term replace(Term term, Term with, IntIterator it,
            Services services, SVInstantiations svInst, 
            Sort maxSort) {     
        if (it.hasNext()) {         
            int sub = it.next();
            
            ImmutableArray<QuantifiableVariable>[] origvars = 
                new ImmutableArray[term.arity()];
            final Term[] subs = new Term[term.arity()];
            
            boolean containsBoundVar = false;
            for (int i=0, arity = term.arity(); i<arity; i++) {
                final Term tSub = term.sub(i);
                if (i!=sub) {
                    subs[i] = tSub;
                } else {                    
                    final Sort newMaxSort;
                    if (term.op() instanceof Function) {
                        newMaxSort = 
                            ((Function)term.op()).argSort(i);
                    } else {
                        newMaxSort = tSub.sort();
                    }
                    subs[i] = replace(tSub, with, it, services, 
                            svInst, newMaxSort);
                }
                origvars[i] = term.varsBoundHere(i);
                
                if (origvars[i].size()>0) {
                    containsBoundVar = true;
                }
            }                                           
            
            if (!containsBoundVar) {
                // for quantified updates there seems to be a distinction
                // if no variables are quantified or quantification over 
                // the empty set
                origvars = null;
            }
            
            return TermFactory.DEFAULT.createTerm(term.op(), 
                    subs,
                    origvars,
                    term.javaBlock());
        } 
        
        with = syntacticalReplace(with, services, svInst);        
        
        
        if (maxSort instanceof AbstractSort) {
            boolean noCastNecessary = with.sort().extendsTrans(maxSort);
            if (!noCastNecessary) {
                with = TermFactory.DEFAULT.
                createCastTerm((AbstractSort)maxSort, with);
            }
        } else {
//          maybe move getCastSymbol to sort interface 
//          in the meantime no casts are inserted
        }
        
        return with;
    }

    
    
    
    
    
    
    
    
    //------------------------------------------------------------------------
    
        
    
    public class MethodReferenceWalker extends JavaASTWalker {
        private LinkedList methodRefs;

        public MethodReferenceWalker(ProgramElement root) {
            super(root);
            methodRefs= new LinkedList();
        }

        public LinkedList containsMethodRef() {
            return methodRefs;
        }

        public void doAction(ProgramElement node) {
            if (node instanceof MethodReference) {
                methodRefs.add(node);
            }
        }
    }


    /** Determines the occurrence of a Java 
     *  block in a Sequent by the number of 
     *  the Java blocks that are "on the left" of the Java block
     */
    public class Occ{

        public boolean ant;
        /**Occurrence of the formula in the subsequent*/
        public int cfm;
        /**This is unclear. Is this the "Subformula Occurence" of the term
         * with the JavaBlock (according to Def. 4) or is it rather a 
         * "Java Block Occurence in a Formula" (according to Def. 5). 
         * getSubformulaOccurrence seems to give a "Java Block Occurence in a formula"
         * but getOccurrenceOfJavaBlock seems to give a "Subformula Occurrence".
         * See Minor Thesis of Markus Baum.*/
        public int jb;
        /** The term containing the JavaBlock that is described by this occurence object. 
         * This term should have the runtime type ProgramTerm, but ProgramTerm is not
         * visible in this package (There is maybe a reason for it). */
        public Term jbt; 
        
        /** @param ant determines if the Java block occures in 
         *         the antecedent or succedent of the sequent
         *  @param cfm the index of the formula in the semisequent
         *  @param jb determines the occurrence of the Java block
         *         in the formula
         */  
        public Occ(boolean ant, int cfm, int jb){
            set(ant, cfm, jb);
        }
       
        /**This is an extended constructor that is used by 
         * VisualizationStrategyForTesting. 
         * @author gladisch*/
        public Occ(boolean ant, int cfm, int jb, Term jbt){
            this(ant,cfm,jb);
            if(jbt==null){
                throw new RuntimeException("Term with JavaBlock is not specified.");
            }
            this.jbt = jbt;
        }
        
        public void copy(Occ occ) {
            set(occ.ant, occ.cfm, occ.jb, occ.jbt);            
        }

        public void set(boolean p_ant, int p_cfm, int p_jb) {
            this.ant = p_ant;
            this.cfm = p_cfm;
            this.jb  = p_jb;
        }

        public void set(boolean p_ant, int p_cfm, int p_jb, Term p_jbt) {
            set(p_ant,p_cfm,p_jb);
            this.jbt  = p_jbt;
        }

        public Occ copy() {
            if(jbt==null){
                //it is allowed to not instantiate jbt in the new occ if this original occ didn't have jbt instantiated.
                return new Occ(ant, cfm, jb);
            }else{
                //If this occ has jbt instantiated then its copy has to have jbt instantiated as well.
                //Otherwise the constructor throws an exception.
                return new Occ(ant, cfm, jb, jbt);
            }
        }
        
        public String toString(){
            return ("Occurrence: "+ ant+" / "+cfm+ " / "+ jb);
        }
    }
    

    /** Determines the occurrence of  a Java block in
     *  an instantiated schema variable or 
     *  determines the schematic
     *  Java block 
     */
    
    class OccInSchema{
        public boolean isJavaBlock= false;
        public JavaBlock jb;
        public  int occ=-1;
        public SchemaVariable sv=null;

             public OccInSchema(JavaBlock jb){
                 this.jb = jb;
                 occ=0;
                 isJavaBlock = true;
             }
             public OccInSchema(SchemaVariable sv, int svOcc){
                 this.sv= sv; 
                 this.occ = svOcc;
             }

             public String toString(){
                 if (isJavaBlock) {
                    return "Occ in Java block: "+jb;
                } else {
                    return ("Occ in SV: "+sv +" "+occ+" "+isJavaBlock);
                }
             }
             
    }
    
    
    

    public class StatementByPositionWalker extends JavaASTWalker {

        ProgramElement result = null;

        PositionInfo toFind = null;

        public StatementByPositionWalker(ProgramElement root, PositionInfo toFind) {
            super(root);
             this.toFind = toFind;
        }

        public void doAction(ProgramElement node) {
             if (node.getPositionInfo().equals(toFind) ) {
                result = node;
            }

        }

        public SourceElement getResult() {
            return result;
        }
    }
    
}

