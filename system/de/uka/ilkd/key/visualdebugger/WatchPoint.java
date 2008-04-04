package de.uka.ilkd.key.visualdebugger;

import java.util.List;

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
}
