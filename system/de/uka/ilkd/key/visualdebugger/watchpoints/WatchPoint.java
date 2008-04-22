package de.uka.ilkd.key.visualdebugger.watchpoints;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;

/**
 * The Class WatchPoint.
 */
public class WatchPoint {

    /** The name of the temporary variable in the file. ... boolean name_of_watchpoint = expr; */
    private final String name;
    
    /** The watch expression. */
    private final String expression;
    
    /** The type in which the expression was set. */
    private final String declaringType;
    
    /** The method in which the expression was set. For fields it will be set to "Field theField". */
    private final String method;
    
    /** The line where the watchpoint was set. */
    private final int statement_line;
    
    /** The local variables. */
    private final List<LocalVariableDescriptor> localVariables;
    
    /** The enabled. */
    private boolean enabled = true;

    private List<String> parameterTypes;
    /** The watchpoint parsed as KeY data structure. */
    private Term watchpointAsTerm;
    /** The method where the local variables belong to.*/
    private ProgramMethod programMethod = null;
    /** The positions where the local variables occurred in the method.*/
    private List<Integer> keyPositions = new LinkedList<Integer>();
    /** A list of local variables used in this watchpoint. */
    private List<LocationVariable> orginialLocalVariables = new LinkedList<LocationVariable>();
  
    /**
     * Gets the in type.
     * 
     * @return the in type
     */
    public String getInType() {
        return declaringType;
    }
    
    /**
     * Instantiates a new watch point.
     * 
     * Use this constructor to instaniate a new watch point for a global field or a constant.
     * 
     * @param wpd the WatchpointDescriptor encapsulating watchpoint related information
     */
    public WatchPoint(WatchpointDescriptor wpd) {
        super();
        this.name = wpd.getVarName();
        this.expression = wpd.getExpression();
        this.method = wpd.getDeclaringMethod();
        this.statement_line = wpd.getLine();
        this.declaringType = wpd.getDeclaringType();
        this.localVariables = wpd.getLocalVariables();
        this.parameterTypes = wpd.getParameterTypes();
        
    }
    
    /**
     * Gets the expression.
     * 
     * @return the expression
     */
    public String getExpression() {
        return expression;
    }
    
    /**
     * Gets the file.
     * 
     * @return the file
     */
    public String getDeclaringType() {
        return declaringType;
    }

    /**
     * Gets the method.
     * 
     * @return the method
     */
    public String getMethod() {
        return method;
    }


    /**
     * Gets the statement_line.
     * 
     * @return the statement_line
     */
    public int getStatement_line() {
        return statement_line;
    }


    /**
     * Gets the name.
     * 
     * @return the name
     */
    public String getName() {
        return name;
    }

    /**
     * Checks if is enabled.
     * 
     * @return true, if is enabled
     */
    public boolean isEnabled() {
        return enabled;
    }

    /**
     * Sets the Watchpoint enabled.
     * 
     * @param isEnabled the new enabled
     */
    public void setEnabled(boolean isEnabled) {
        this.enabled = isEnabled;
    }
    
    /**
     * Gets the local variables.
     * 
     * @return the local variables
     */
    public List<LocalVariableDescriptor> getLocalVariables() {
        return localVariables;
    }

    public List<String> getParameterTypes() {
        return parameterTypes;
    }

    public void setParameterTypes(List<String> parameterTypes) {
        this.parameterTypes = parameterTypes;
    }

    public Term getWatchpointAsTerm() {
        return watchpointAsTerm;
    }

    public void setWatchpointTerm(Term watchpointAsTerm) {
        this.watchpointAsTerm = watchpointAsTerm;
    }

    public List<LocationVariable> getOrginialLocalVariables() {
        return orginialLocalVariables;
    }

    public void setOrginialLocalVariables(
            List<LocationVariable> orginialLocalVariables) {
        this.orginialLocalVariables = orginialLocalVariables;
    }

    public ProgramMethod getProgramMethod() {
        return programMethod;
    }

    public void setProgramMethod(ProgramMethod programMethod) {
        this.programMethod = programMethod;
    }

    public List<Integer> getKeyPositions() {
        return keyPositions;
    }

    public void setKeyPositions(List<Integer> keyPositions) {
        this.keyPositions = keyPositions;
    }


}
