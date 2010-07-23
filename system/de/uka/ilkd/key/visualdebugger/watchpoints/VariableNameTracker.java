// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.watchpoints;

import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;
/**
 * This Class offers several tools to keep track of (local) variable names, 
 * since they are renamed during a proof. Renamed variables are new objects.
 * After an instances of this class was started the method result() returns
 * a map, where each entry holds the current names for variables for a specific
 * program method. Note that this class is tailored for usage in context with
 * watchpoints.
 * 
 */
public class VariableNameTracker {

    /** The current proof tree.*/
    private Node node;
    /** The watchpoints.*/
    private List<WatchPoint> watchpoints;
    private ImmutableList<Node> branch = null;
    private Map<ProgramMethod, ImmutableList<RenamingTable>> nameMaps = new HashMap<ProgramMethod, ImmutableList<RenamingTable>>();
    private Stack<ProgramMethod> methodStack = new Stack<ProgramMethod>();
    private Stack<ReferencePrefix> selfVarStack = new Stack<ReferencePrefix>();
    private ReferencePrefix selfVar = null;
    /**The method we are currently in.*/
    private ProgramMethod activeMethod = null;
    
    /**
     * Instantiates a new VariableNameTracker.
     * 
     * @param node - the current proof tree
     * @param watchpoints - a list of watchpoints
     */
    public VariableNameTracker(Node node, List<WatchPoint> watchpoints) {
        super();
        this.node = node;
        this.watchpoints = watchpoints;
        branch = buildBranch(node);
    }


    /**
     * @param node
     */
    private SourceElement getStatement(Node node) {
        try {

            Iterator<ConstrainedFormula> iterator = node.sequent().iterator();
            ConstrainedFormula constrainedFormula;
            Term term;
            while (iterator.hasNext()) {
                constrainedFormula = iterator.next();
                term = constrainedFormula.formula();

                while (term.op() instanceof QuanUpdateOperator) {
                    int targetPos = ((QuanUpdateOperator) term.op())
                    .targetPos();
                    term = term.sub(targetPos);
                }
                // proceed to most inner method-frame
                if (term.op() instanceof Modality) {
                    ProgramPrefix programPrefix = (ProgramPrefix) term
                    .javaBlock().program();
                    return programPrefix.getPrefixElementAt(programPrefix
                            .getPrefixLength() - 1);
                }
            }
        } catch (RuntimeException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        return null;
    }
   
    
    /**
     * Gets the indices of all parameters that are used in (all) watchpoints for the
     * given method.
     * 
     * @param programMethod
     *                the program method
     * 
     * @return the parameter indices of method, null if no local variables are
     *         used
     */
    private Set<Integer> getParameterIndicesOfMethod(
            ProgramMethod programMethod) {

        int parameterCount = programMethod.getParameterDeclarationCount();
        Set<Integer> parameterIndices = new HashSet<Integer>();

        for (WatchPoint watchPoint : getWatchpointsForMethod(programMethod)) {

                for (int position : watchPoint.getKeyPositions()) {

                    if( position < parameterCount) {
                        parameterIndices.add(position);
                    }
                }
        }
        return parameterIndices;
    }
 
    /**
     * Checks if the given listOfRuleSet contains the method-expand taclet.
     * 
     * */
    private boolean isMethodExpandRule(ImmutableList<RuleSet> listOfRuleSet) {
        return listOfRuleSet.contains(
                new RuleSet(
                        new Name("method_expand")));
    }
    /**
     * Add parameter count.
     *
     *  In this method the we add the parametercount on the position of the variables from the method
     *  body. After that the correct order of the variables is rebuild according to the original ones.
     * 
     * @param programMethod the program method
     * @param variables the variables
     * @param parameterCount the parameter count
     * @param watchpoints the watchpoints
     * 
     * @return the renamed local variables
     */
    private List<LocationVariable> addParameterCount(
            ProgramMethod programMethod, Map<Integer, SourceElement> variables,
            int parameterCount, List<WatchPoint> watchpoints) {

        Set<Entry<Integer, SourceElement>> entrySet = variables.entrySet();
        List<LocationVariable> localVariables = new LinkedList<LocationVariable>();
        
        for (WatchPoint watchPoint : getWatchpointsForMethod(programMethod)){
                for (int position : watchPoint.getKeyPositions()) {
                    for (Entry<Integer, SourceElement> entry : entrySet) {
                        if (entry.getKey() + parameterCount == position) {
                            VariableSpecification varspec = (VariableSpecification) entry.getValue();
                            localVariables.add((LocationVariable) varspec.getProgramVariable());
                        }
                    }
                }
        }
        return localVariables;
    }

    /**
     * builds a branch from the root to the given node
     * 
     * @param n - an arbitrary node
     * @return a list of nodes from the root the passed node
     */
    private ImmutableList<Node> buildBranch(Node n) {
        ImmutableList<Node> lon = ImmutableSLList.<Node>nil();
        while(n.parent() != null){
            lon = lon.append(n);
            n=n.parent();
        }
        return lon.reverse();
    }
    /**
     * updates the MethodStack.
     * checks for a given node pair if methods returned and if
     * so, it removes the corresponding entry from the name map
     * 
     * @param current
     * @param child
     * @param nameMap
     */
    private void updateMethodStack(Node current, Node child, Map<ProgramMethod, ImmutableList<RenamingTable>> nameMap) {
        try {
            
            int current_stacksize = VisualDebugger.getVisualDebugger()
                    .getMethodStackSize(current);
            int next_stacksize = VisualDebugger.getVisualDebugger()
                    .getMethodStackSize(child);
            
            if (current_stacksize == -1 || next_stacksize == -1)    return;
            
            if (current_stacksize > next_stacksize) {
                int diff = current_stacksize - next_stacksize;
                for (int k = 0; k < diff; k++) {
                    if (!methodStack.isEmpty()) {
                       selfVarStack.pop();
                       ProgramMethod key =  methodStack.pop();
                       if(nameMap.containsKey(key)){
                       ImmutableList<RenamingTable> lort = nameMap.get(key);
                       lort = lort.removeFirst(lort.head());
                       nameMap.put(key, lort);
                       }
                       selfVar.toString();
                       methodStack.toString();
                    }
                }
            }
        } catch (EmptyStackException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }

    /**
     * Update self variable for local watchpoints. 
     * The method keeps track of the this pointer.
     * Note that a null element is pushed on the stack, if
     * the method-frame belongs to a static method.
     * @see #getSelfVar()
     * 
     * @param mf the MethodFrame
     */
    private void updateSelfVar(MethodFrame mf) {
        ExecutionContext executionContext = (ExecutionContext) mf.getExecutionContext();
        // the execution context might be null for static methods
        selfVar = executionContext.getRuntimeInstanceAsRef();
        // if the execution context was null, we push a null element and create 
        // skip update later on
        selfVarStack.push(selfVar);
    }


    /**
     * Collect all renamings from the current proof tree.
     * 
     * @return the list of renaming table
     */
    private ImmutableList<RenamingTable> collectAllRenamings() {

        ImmutableList<RenamingTable> allRenamings = ImmutableSLList.<RenamingTable>nil();

        for (Node aBranch : branch) {
            Node currentNode = aBranch;
            ImmutableList<RenamingTable> renamingTables = currentNode.getRenamingTable();
            if (renamingTables != null && renamingTables.size() > 0) {
                System.out.println("found renaming @node: " + currentNode.serialNr());

                for (RenamingTable renamingTable : renamingTables) {
                    RenamingTable next = renamingTable;
                    System.out.println(next); //TODO remove
                    allRenamings = allRenamings.append(next);
                }
            }
        }
        return allRenamings;
    }
    
    /**
     * Track variable names.
     * 
     * @param pm the pm
     * @param initialRenamings the initial renamings
     * 
     * @return the renaming table
     */
    private RenamingTable trackVariableNames(ProgramMethod pm, List<LocationVariable> initialRenamings) {

        List<LocationVariable> originalLocalVariables = getLocalsForMethod(pm);
        
        HashMap<LocationVariable, SourceElement> nameMap = new HashMap<LocationVariable, SourceElement>();
      
//        List<LocationVariable> originalLocalVariables = Arrays.asList(olv
//                .toArray(new LocationVariable[olv.size()]));
        
        // every local variable needs a corresponding renamed counterpart
        assert originalLocalVariables.size() == initialRenamings.size();

        for(int k = 0; k<originalLocalVariables.size(); k++) {
            // create standard mapping from original var -> initially renamed var
            LocationVariable originalVar = originalLocalVariables.get(k);
            LocationVariable initiallyRenamedVar = initialRenamings.get(k);
            nameMap.put(originalVar, initiallyRenamedVar);
            System.out.println("created initial mapping");

            for (RenamingTable renamingTable : collectAllRenamings()) {
                RenamingTable renaming = renamingTable;

                SourceElement renamedVariable = renaming
                        .getRenaming(initiallyRenamedVar);

                if (renamedVariable != null) {
                    // replace entry with the most actual one
                    nameMap.put(originalVar, renamedVariable);
                    System.out.println("created name update");
                }
                //trackHistory(nameMap);
            }
        }
        return new MultiRenamingTable(nameMap);
    }
    //TODO the method is buggy and causes a stack overflow
    // it does not terminate because the values are not "disappearing" from the namemap
    private void trackHistory(HashMap<LocationVariable, SourceElement> nameMap) {
        
        Iterator<RenamingTable> i = collectAllRenamings().iterator();
        boolean allNamesUpToDate = true;
        while (i.hasNext()) {
            RenamingTable renaming = i.next();

            for (SourceElement name : nameMap.values()) {
                SourceElement renamedVariable = renaming
                .getRenaming(name);

                if (renamedVariable != null) {
                    // replace entry with the most actual one
                    allNamesUpToDate = false;
                    System.out.println("traced name...");
                    nameMap.put((LocationVariable) name, renamedVariable);
                }
            }
        }if(allNamesUpToDate){return;} else {trackHistory(nameMap); }
    }
/**
 * some helper methods 
 */

    private void addRenamingTable(ProgramMethod key, Map<ProgramMethod, ImmutableList<RenamingTable>> nameMap, RenamingTable newElement){
        ImmutableList<RenamingTable> lort = nameMap.get(key);
        lort = nameMap.get(key).prepend(newElement);
        nameMap.put(key, lort);
        }
    
    private List<LocationVariable> getAllLocalVariables(/*List<WatchPoint> watchpoints*/){
        List<LocationVariable> locals = new LinkedList<LocationVariable>();
        for (WatchPoint watchPoint : watchpoints) {
            locals.addAll(watchPoint.getOrginialLocalVariables());
            }
        return locals;
    }
    
    private List<LocationVariable> getLocalsForMethod(ProgramMethod pm){
        List<LocationVariable> locals = new LinkedList<LocationVariable>();
        for (WatchPoint watchPoint : watchpoints) {
            if(watchPoint.getProgramMethod().equals(pm)) {
                
                List<LocationVariable> currentlocals = watchPoint.getOrginialLocalVariables();
                for (LocationVariable locationVariable : currentlocals) {
                    // add distinct
                    if (!locals.contains(locationVariable))
                        locals.add(locationVariable);
                }
            }
        }
        return locals;
    }
    
    private List<WatchPoint> getWatchpointsForMethod(ProgramMethod pm){
        List<WatchPoint> wps = new LinkedList<WatchPoint>();
        for (WatchPoint watchPoint : watchpoints) {
            
            ProgramMethod programMethod = watchPoint.getProgramMethod();
            if(programMethod!= null && programMethod.equals(pm))
            wps.add(watchPoint);
            }
        return wps;
    }
    
    /**
     * Starts the name tracker.
     * 
     * When the KeY Prover is started every variable is initially renamed by the ProgVarReplaceVisitor, i.e. it
     * is a new object. If we have used local variables in the watchpoints we have
     * to keep track of these renamings. Therefore this method first looks up all applications of method-expand taclets.
     * In those methods we check first if they contain parameters that are relevant for us and furthermore store the
     * parameter count. Finally the following method-frame is investigated and the parameter count added to each variable found
     * in the method-frame to rebuild the original order.
     * 
     */
    public void start() {

        try {
            final Services services = node.proof().getServices();

            List<LocationVariable> renamedLocalVariables = null;
            ProgramMethod programMethod = null;
            int parameterCount = 0;

            Iterator<Node> i = branch.iterator();
            // 2 nodes needed to compare something at all
            assert branch.size() >= 2;
            Node current = i.next();
            while (i.hasNext()) {

                Node child = i.next();
                updateMethodStack(current, child, nameMaps);

                if (current.getAppliedRuleApp().rule() instanceof Taclet) {

                    if (isMethodExpandRule(((Taclet) current
                            .getAppliedRuleApp().rule()).getRuleSets())) {

                        renamedLocalVariables = new LinkedList<LocationVariable>();
                        // treat parent, i.e. the method-body-statement to get
                        // parameter information
                        SourceElement parentElement = getStatement(current);
                        MethodBodyStatement mbs = null;
                        if (parentElement instanceof StatementContainer) {

                            mbs = (MethodBodyStatement) parentElement
                                    .getFirstElement();
                            programMethod = mbs.getProgramMethod(node.proof()
                                    .getServices());
                            // keep method stack up to date
                          //  if(isMethodOfInterest(programMethod));
                            methodStack.push(programMethod);
                            activeMethod=programMethod;
                            System.out.println(methodStack.size()
                                    + " elements on stack after push");
                            if (!nameMaps.containsKey(programMethod)) {
                                nameMaps.put(programMethod,
                                        ImmutableSLList.<RenamingTable>nil());
                            }
                        }

                        parameterCount = programMethod
                                .getParameterDeclarationCount();
                        Set<Integer> parameterIndices = getParameterIndicesOfMethod(programMethod);

                        for (Integer index : parameterIndices) {

                            LocationVariable programVariable = (LocationVariable) mbs
                                    .getArguments().get(index);
                            renamedLocalVariables.add(programVariable);
                        }

                        // treat currentnode, i.e. the method-frame
                        SourceElement element = getStatement(child);
                        // Before getting the finally renamed variables we have
                        // to get all variables that are declared
                        // in the method body. The resulting positions are not
                        // correct yet since the parameter count is missing.
                        if (element instanceof MethodFrame) {

                            MethodFrame mf = (MethodFrame) element;
                            MethodVisitor mv = new MethodVisitor(mf, services);
                            mv.start();
                            System.out.println(mf.getExecutionContext());
                            
                            updateSelfVar(mf);
                            renamedLocalVariables.addAll(addParameterCount(
                                    programMethod, WatchpointUtil.valueToKey(mv
                                            .result()), parameterCount,
                                    watchpoints));
                        }
                        System.out.println("size of renamed variables: "
                                + renamedLocalVariables.size());
                        if (renamedLocalVariables.isEmpty()) {
                            nameMaps.remove(programMethod);
                            System.out.println("removed mbs");
                        } else {

                            addRenamingTable(programMethod, nameMaps,
                                    trackVariableNames(programMethod,
                                            renamedLocalVariables));
                        }
                    }
                }
                current = child;
            }
        } catch (RuntimeException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
    }
    
 public Map<ProgramMethod, ImmutableList<RenamingTable>> result (){
     return nameMaps;
 }

/**
 * Gets the self variable.
 * Returns the peek element from the selfVarStack.
 * Note that the returned element might be null in
 * case a static method has been called
 * 
 * @see #updateSelfVar(MethodFrame)
 * @return the self var
 */
public ReferencePrefix getSelfVar() {
    return selfVarStack.peek();
}


public ProgramMethod getActiveMethod() {
    return activeMethod;
}  
private boolean isMethodOfInterest(ProgramMethod pm){
    for (WatchPoint wp : watchpoints) {
        if(wp.getProgramMethod().equals(pm)) return true;
    }
    return false;
}
 
}
