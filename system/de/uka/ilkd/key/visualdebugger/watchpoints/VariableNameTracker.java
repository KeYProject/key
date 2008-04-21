package de.uka.ilkd.key.visualdebugger.watchpoints;

import java.util.*;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementContainer;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.QuanUpdateOperator;
import de.uka.ilkd.key.proof.IteratorOfNode;
import de.uka.ilkd.key.proof.ListOfNode;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.SLListOfNode;
import de.uka.ilkd.key.rule.ListOfRuleSet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;

public class VariableNameTracker {

    /** The current proof tree.*/
    private Node node;
    /** The watchpoints.*/
    private List<WatchPoint> watchpoints;
    
    private Map<MethodBodyStatement, ListOfRenamingTable> nameMaps = new HashMap<MethodBodyStatement, ListOfRenamingTable>();
    
    public VariableNameTracker(Node node, List<WatchPoint> watchpoints) {
        super();
        this.node = node;
        this.watchpoints = watchpoints;
    }


    /**
     * @param node
     */
    private SourceElement getStatement(Node node) {
        try {

            IteratorOfConstrainedFormula iterator = node.sequent().iterator();
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
     * Gets the indices of all parameters that are used in (all)watchpoints for the
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
    private boolean isMethodExpandRule(ListOfRuleSet listOfRuleSet) {
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
     * Gets the initial renamings.
     * 
     * When the KeY Prover is started every variable is initially renamed by the ProgVarReplaceVisitor, i.e. it
     * has still the same "name" but it is a new object. If we have used local variables in the watchpoints we have
     * to keep track of these renamings. Therefore this method first looks up all applications of method-expand taclets.
     * In those methods we check first if they contain parameters that are relevant for us and furthermore store the
     * parameter count. Finally the following method-frame is investigated and the parameter count added to rebuild
     * the original order.
     * 
     * @param node the node
     */
    public void start() {

        Node currentNode = node;
        Node parent = currentNode.parent();
        List<LocationVariable> renamedLocalVariables = null;
        List<LocationVariable> initialRenamings = new LinkedList<LocationVariable>();
        ProgramMethod programMethod = null;
        int parameterCount = 0;

        while (parent != null) {

            if (parent.getAppliedRuleApp().rule() instanceof Taclet) {

                if (isMethodExpandRule(((Taclet) parent.getAppliedRuleApp()
                        .rule()).getRuleSets())) {
                    
                    renamedLocalVariables = new LinkedList<LocationVariable>();
                    // treat parent, i.e. the method-body-statement to get parameter information
                    SourceElement parentElement = getStatement(parent);
                    MethodBodyStatement mbs = null;
                    if (parentElement instanceof StatementContainer) {

                        mbs = (MethodBodyStatement) parentElement.getFirstElement();
                        if(!nameMaps.containsKey(mbs)){
                            System.out.println("added mbs to name map");
                            nameMaps.put(mbs, SLListOfRenamingTable.EMPTY_LIST);
                        }
                         programMethod = mbs.getProgramMethod(node.proof()
                                .getServices());
                    }

                    parameterCount = programMethod.getParameterDeclarationCount();
                    Set<Integer> parameterIndices = getParameterIndicesOfMethod(programMethod);

                    for (Integer index : parameterIndices) {
                        
                        LocationVariable programVariable = (LocationVariable) mbs.getArguments().getExpression(index);
                        renamedLocalVariables.add(programVariable);
                        initialRenamings.add(programVariable);
                    }
                    
                    // treat currentnode, i.e. the method-frame
                    SourceElement element = getStatement(currentNode);
                    //  Before getting the finally renamed variables we have to get all variables that are declared
                    //  in the method body. The resulting positions are not correct yet since the parameter count is missing.
                    if (element instanceof MethodFrame) {
                       
                        MethodVisitor mv = new MethodVisitor(
                                (MethodFrame) element);
                        mv.start();
                        
                        renamedLocalVariables.addAll(addParameterCount(
                                programMethod, WatchpointUtil.valueToKey(mv.result()),
                                parameterCount, watchpoints));
                        initialRenamings.addAll(addParameterCount(
                                programMethod, WatchpointUtil.valueToKey(mv.result()),
                                parameterCount, watchpoints));

                    }System.out.println("size of renamed variables: " + renamedLocalVariables.size());
                    if(renamedLocalVariables.isEmpty()){
                        nameMaps.remove(mbs);
                        System.out.println("removed mbs");
                    }else {
                    addRenamingTable(mbs, nameMaps, trackVariableNames(programMethod, renamedLocalVariables));
                }
                    }
            }
            currentNode = parent;
            parent = currentNode.parent();
        }System.out.println("size of renamed variables: " + renamedLocalVariables.size());
    }
    
    private ListOfRenamingTable collectAllRenamings() {

        ListOfRenamingTable allRenamings = SLListOfRenamingTable.EMPTY_LIST;
        Node anode = node;
        // climb the tree
        ListOfNode lon = SLListOfNode.EMPTY_LIST;
        while (anode.parent() != null) {
            
            lon = lon.append(anode.parent());
            anode = anode.parent();
        }
        lon = lon.reverse();
        // walk back on the same branch
        IteratorOfNode it = lon.iterator();
        while (it.hasNext()) {
            Node currentNode = it.next();
            ListOfRenamingTable renamingTables = currentNode.getRenamingTable();
            if (renamingTables != null && renamingTables.size() > 0) {
                System.out.println("found renaming @node: " + currentNode.serialNr());
                IteratorOfRenamingTable i = renamingTables.iterator();

                while (i.hasNext()) {
                    RenamingTable next = i.next();
                    System.out.println(next);
                    allRenamings = allRenamings.append(next);
                }
            }

        }
        return allRenamings;
    }
    
    private RenamingTable trackVariableNames(ProgramMethod pm, List<LocationVariable> initialRenamings) {

        List<LocationVariable> orginialLocalVariables = getLocalsForMethod(pm);
        HashMap<LocationVariable, SourceElement> nameMap = new HashMap<LocationVariable, SourceElement>();

        assert orginialLocalVariables.size() == initialRenamings.size();

        for(int k = 0; k<orginialLocalVariables.size(); k++) {
            // create standard mapping from original var -> initially renamed var
            LocationVariable originalVar = orginialLocalVariables.get(k);
            LocationVariable initiallyRenamedVar = initialRenamings.get(k);
            nameMap.put(originalVar, initiallyRenamedVar);
            System.out.println("created initial mapping");
            IteratorOfRenamingTable i = collectAllRenamings().iterator();

            while (i.hasNext()) {
                RenamingTable renaming = i.next();

                SourceElement renamedVariable = renaming
                .getRenaming(initiallyRenamedVar);

                if (renamedVariable != null) {
                    // replace entry with the most actual one
                    nameMap.put(originalVar, renamedVariable);
                    System.out.println("created name update");

                }
                //TODO track history
              //  trackHistory(nameMap);
            }
        }
        return new MultiRenamingTable(nameMap);
    }
    //TODO
    private void trackHistory(HashMap<LocationVariable, SourceElement> nameMap) {
       
        IteratorOfRenamingTable i = collectAllRenamings().iterator();
        boolean allNamesUpToDate = true;
        while (i.hasNext()) {
            RenamingTable renaming = i.next();

            for (SourceElement name : nameMap.values()) {
                SourceElement renamedVariable = renaming
                .getRenaming(name);

                if (renamedVariable != null) {
                    // replace entry with the most actual one
                    allNamesUpToDate = false;
                    nameMap.put((LocationVariable) name, renamedVariable);
                }
            }
        }if(allNamesUpToDate){return;} else {trackHistory(nameMap); }
    }
/**
 * some helper methods 
 */

    private void addRenamingTable(MethodBodyStatement key, Map<MethodBodyStatement, ListOfRenamingTable> nameMap, RenamingTable newElement){
        ListOfRenamingTable lort = nameMap.get(key);
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
            if(watchPoint.getProgramMethod().equals(pm))
            locals.addAll(watchPoint.getOrginialLocalVariables());
            }
        return locals;
    }
    private List<WatchPoint> getWatchpointsForMethod(ProgramMethod pm){
        List<WatchPoint> wps = new LinkedList<WatchPoint>();
        for (WatchPoint watchPoint : watchpoints) {
            if(watchPoint.getProgramMethod().equals(pm))
            wps.add(watchPoint);
            }
        return wps;
    }
    
 public Map<MethodBodyStatement, ListOfRenamingTable> result (){
     return nameMaps;
 }  
 
}
