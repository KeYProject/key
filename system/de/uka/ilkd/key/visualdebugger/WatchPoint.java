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
    private final String statement_line;
    
    /** The local variables. */
    private final List<String[]> localVariables;
    
    /** The enabled. */
    private boolean enabled = true;
  
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
     * @param expression the expression
     * @param declaringType the type in which the watchpoint was set
     * @param method the method
     * @param statement_line the statement_line
     * @param localVariables the local variables
     * @param name the name
     */
    public WatchPoint(String name, String expression, String method,
            String statement_line, String declaringType, List<String[]> localVariables) {
        super();
        this.name = name;
        this.expression = expression;
        this.method = method;
        this.statement_line = statement_line;
        this.declaringType = declaringType;
        this.localVariables = localVariables;
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
    public String getTypeOfSource() {
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
    public String getStatement_line() {
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
    public List<String[]> getLocalVariables() {
        return localVariables;
    }
}
