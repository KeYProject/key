package de.uka.ilkd.key.visualdebugger.watchpoints;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
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
import de.uka.ilkd.key.rule.updatesimplifier.Update;

public class VariableNameTracker {

    /** The current proof tree.*/
    private Node node;
    /** The watchpoints.*/
    private List<WatchPoint> watchpoints;
    
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
     * Gets the indices of all parameters that are used in watchpoints for the
     * given method.
     * 
     * @param programMethod
     *                the program method
     * 
     * @return the parameter indices of method, null if no local variables are
     *         used
     */
    private List<Integer> getParameterIndicesOfMethod(
            ProgramMethod programMethod) {

        int parameterCount = programMethod.getParameterDeclarationCount();
        List<Integer> parameterIndices = new LinkedList<Integer>();

        for (WatchPoint watchPoint : watchpoints) {
            if(watchPoint.getProgramMethod().equals(programMethod)){
                for (int position : watchPoint.getKeyPositions()) {

                    if( position < parameterCount) {
                        System.out.println("adding parameterposition" + position);
                        parameterIndices.add(position);
                    }
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
     * Gets the renamed local variables.
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

        for (WatchPoint watchPoint : watchpoints) {
            if(watchPoint.getProgramMethod().equals(programMethod)){
                for (int position : watchPoint.getKeyPositions()) {
                    for (Entry<Integer, SourceElement> entry : entrySet) {
                        if (entry.getKey() + parameterCount == position) {
                            System.out.println("added var");
                            VariableSpecification varspec = (VariableSpecification) entry.getValue();
                            localVariables.add((LocationVariable) varspec.getProgramVariable());
                        }
                    }
                }
            }
        }System.out.println("apc "+localVariables.size());
        return localVariables;
    }
    /**
     * This method checks for every watchpoints local variables if they are already in the global
     * namespace of the node representing the current proof and thus cannot be located using the renaming tables. 
     * It returns the proper updates for each variable that is contained in the namespace <br><br>
     * {original_var:=initiallyRenamed_var}
     *  
     * @param updateFactory
     * @param updates
     */
    public void checkNamespace(UpdateFactory updateFactory, LinkedList<Update> updates, List<LocationVariable> inittiallyRenamedLocalVariables) {

        for(WatchPoint wp : watchpoints){
            for(int i = 0;  i < wp.getOrginialLocalVariables().size(); i++){
                System.out.println("checking var" + i);
                if(!inittiallyRenamedLocalVariables.isEmpty()){
                LocationVariable orginialVariable = wp.getOrginialLocalVariables().get(i);
                LocationVariable renamedVariable = inittiallyRenamedLocalVariables.get(i);
                System.out.println("xx ren  var "+ renamedVariable +" " + renamedVariable.id());
                    
                    if(node.getGlobalProgVars().contains(renamedVariable ) ){
                        System.out.println("var found in global namespace " + renamedVariable);
                        updates.add(updateFactory.elementaryUpdate(
                                TermFactory.DEFAULT.createVariableTerm(orginialVariable),
                                TermFactory.DEFAULT.createVariableTerm(renamedVariable)));
                }

            }}
        }
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
     * 
     * @return the initial renamings
     */
    public List<LocationVariable> getInitialRenamings() {

        Node currentNode = node;
        Node parent = currentNode.parent();
        List<LocationVariable> renamedLocalVariables = new LinkedList<LocationVariable>();
        ProgramMethod programMethod = null;
        int parameterCount = 0;

        while (parent != null) {

            if (parent.getAppliedRuleApp().rule() instanceof Taclet) {

                if (isMethodExpandRule(((Taclet) parent.getAppliedRuleApp()
                        .rule()).getRuleSets())) {
                    System.out.println("found method expand taclet " + parent.serialNr());
                    // treat parent, i.e. the method-body-statement to get parameter information
                    SourceElement parentElement = getStatement(parent);
                    MethodBodyStatement mbs = null;
                    if (parentElement instanceof StatementContainer) {

                        mbs = (MethodBodyStatement) parentElement.getFirstElement();
                        System.out.println(mbs.getMethodReference());
                        System.out.println(mbs.getArguments());
                        programMethod = mbs.getProgramMethod(node.proof()
                                .getServices());
                    }
                    System.out.println("program method "+ programMethod);
                    parameterCount = programMethod.getParameterDeclarationCount();

                    List<Integer> parameterIndices = getParameterIndicesOfMethod(programMethod);

                    for (Integer index : parameterIndices) {
                        
                        
                        LocationVariable programVariable = (LocationVariable) mbs.getArguments().getExpression(index);
                        System.out.println("adding a parameter to list. id " + programVariable.id());
                        renamedLocalVariables.add(programVariable);
                    }
                    // treat currentnode, i.e. the method-frame
                    SourceElement element = getStatement(currentNode);
                    //  Before getting the finally renamed variables we have to get all variables that are declared
                    //  in the method body. The resulting positions are not correct yet since the parameter count is missing.
                    if (element instanceof MethodFrame) {
                        System.out.println("found methodframe " + currentNode.serialNr());
                        MethodVisitor mv = new MethodVisitor(
                                (MethodFrame) element);
                        mv.start();
                        renamedLocalVariables.addAll(addParameterCount(
                                programMethod, WatchpointUtil.valueToKey(mv.result()),
                                parameterCount, watchpoints));
                    }
                }
            }
            currentNode = parent;
            parent = currentNode.parent();
        }System.out.println("size of renamed variables: " + renamedLocalVariables.size());
        return renamedLocalVariables;
    }
    
    public ListOfRenamingTable trackRenaming() {

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
}
