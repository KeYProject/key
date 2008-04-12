package de.uka.ilkd.key.visualdebugger.watchpoints;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.Map.Entry;

import de.uka.ilkd.key.java.SourceElement;
import de.uka.ilkd.key.java.StatementBlock;
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

    private boolean isMethodExpandRule(ListOfRuleSet listOfRuleSet) {
        return listOfRuleSet.contains(
                new RuleSet(
                        new Name("method_expand")));
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
    private LinkedList<Integer> getParameterIndicesOfMethod(
            ProgramMethod programMethod, List<WatchPoint> watchpoints) {

        int parameterCount = programMethod.getParameterDeclarationCount();
        LinkedList<Integer> parameterIndices = new LinkedList<Integer>();

        for (WatchPoint watchPoint : watchpoints) {
            if(watchPoint.getProgramMethod().equals(programMethod)){
                for (int position : watchPoint.getKeyPositions()) {

                    if( position < parameterCount) {
                        parameterIndices.add(position);
                    }
                }
            }
        }
        return parameterIndices;
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

                            VariableSpecification varspec = (VariableSpecification) entry.getValue();
                            localVariables.add((LocationVariable) varspec.getProgramVariable());
                        }
                    }
                }
            }
        }
        return localVariables;
    }
    /**
     * @param node
     * @param watchpoints
     * @param updateFactory
     * @param updates
     */
    public void checkNamespace(Node node, List<WatchPoint> watchpoints,
            UpdateFactory updateFactory, LinkedList<Update> updates) {
        
        for(WatchPoint wp : watchpoints){
            for(int i = 0;  i < wp.getOrginialLocalVariables().size(); i++){
                LocationVariable orginialLocationVariable = wp.getOrginialLocalVariables().get(i);
                LocationVariable renamedLocationVariable = wp.getInittiallyRenamedLocalVariables().get(i);

                if(node.getGlobalProgVars().contains(renamedLocationVariable ) ){

                    System.out.println("+++ detected relevant variable in namespace");

                    updates.add(updateFactory.elementaryUpdate(
                            TermFactory.DEFAULT.createVariableTerm(orginialLocationVariable),
                            TermFactory.DEFAULT.createVariableTerm(renamedLocationVariable)));
                }
            }
        }
    }
    /**
     * Gets the initial renamings.
     * 
     * @param node the node
     * 
     * @return the initial renamings
     */
    public /* List<LocationVariable>*/ void getInitialRenamings(Node node,  List<WatchPoint> watchpoints) {

        Node currentNode = node;
        Node parent = currentNode.parent();
        List<LocationVariable> renamedLocalVariables = new LinkedList<LocationVariable>();
        ProgramMethod programMethod = null;
        int parameterCount = 0;

        while (parent != null) {

            if (parent.getAppliedRuleApp().rule() instanceof Taclet) {

                if (isMethodExpandRule(((Taclet) parent.getAppliedRuleApp()
                        .rule()).getRuleSets())) {

                    // treat parent, i.e. the method-body-statement to get parameter information
                    SourceElement parentElement = getStatement(parent);
                    if (parentElement instanceof StatementBlock) {

                        MethodBodyStatement mbs = (MethodBodyStatement) parentElement
                        .getFirstElement();
                        MethodVisitor mbsVisitor = new MethodVisitor(mbs);
                        mbsVisitor.start();
                        programMethod = mbs.getProgramMethod(node.proof()
                                .getServices());
                        parameterCount = programMethod
                        .getParameterDeclarationCount();

                        LinkedList<Integer> parameterIndices = getParameterIndicesOfMethod(programMethod, watchpoints);

                        for (Integer index : parameterIndices) {
                            renamedLocalVariables.add((LocationVariable) programMethod
                                    .getParameterDeclarationAt(index).getVariableSpecification().getProgramVariable());
                        }
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
                    }

                    for (WatchPoint wp : watchpoints) {
                        if(wp.getProgramMethod().equals(programMethod)){
                            wp.setInittiallyRenamedLocalVariables(renamedLocalVariables);
                        }
                    }
                }
            }
            currentNode = parent;
            parent = currentNode.parent();
        }
        //return renamedLocalVariables;
    }
    public ListOfRenamingTable trackRenaming(Node node, List<WatchPoint> watchpoints) {
    
        ListOfRenamingTable allRenamings = SLListOfRenamingTable.EMPTY_LIST;
    
        // climb the tree
        ListOfNode lon = SLListOfNode.EMPTY_LIST;
        while (node.parent() != null) {
            for (WatchPoint watchPoint : watchpoints) {
                List<LocationVariable> orginialLocalVariables = watchPoint.getOrginialLocalVariables();
                for (LocationVariable locVar : orginialLocalVariables) {
                    Node thatParent = node.parent();
                    Node thatNode = node;
                    try {
    
                        if(thatNode.getGlobalProgVars().contains(locVar)
                                && !thatParent.getGlobalProgVars().contains(locVar)){
    
                            System.out.println("node contains local variable" + node.parent().serialNr());
                        }
                    } catch (RuntimeException e) {
                        // TODO Auto-generated catch block
                        e.printStackTrace();
                    }
                } 
            }
    
            lon = lon.append(node.parent());
            node = node.parent();
    
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
                    allRenamings = allRenamings.append(i.next());
                }
            }
    
        }
        return allRenamings;
    }
}
