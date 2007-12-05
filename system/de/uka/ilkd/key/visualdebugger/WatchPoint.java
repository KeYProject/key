package de.uka.ilkd.key.visualdebugger;


/**
 * The Class WatchPoint.
 */
public class WatchPoint {
    
    /** The watch expression. */
    private String expression;
    
    /** The file in which the expression was set. */
    private String file;
    
    /** The method in which the expression was set. */
    private String method;
    
    /** The statement. */
    private String statement;
    
    /** The scope. */
    private String scope;
    
    /**
     * Instantiates a new watch point.
     * 
     * @param expression the expression
     * @param file the file
     * @param method the method
     * @param statement the statement
     * @param scope the scope
     */
    public WatchPoint(String expression, String scope, String method,
            String statement, String file) {
        super();
        this.expression = expression;
        this.scope = scope;        
        this.method = method;
        this.statement = statement;
        this.file = file;
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
     * Sets the expression.
     * 
     * @param expression the new expression
     */
    public void setExpression(String expression) {
        this.expression = expression;
    }

    /**
     * Gets the file.
     * 
     * @return the file
     */
    public String getFile() {
        return file;
    }

    /**
     * Sets the file.
     * 
     * @param file the new file
     */
    public void setFile(String file) {
        this.file = file;
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
     * Sets the method.
     * 
     * @param method the new method
     */
    public void setMethod(String method) {
        this.method = method;
    }

    /**
     * Gets the statement.
     * 
     * @return the statement
     */
    public String getStatement() {
        return statement;
    }

    /**
     * Sets the statement.
     * 
     * @param statement the new statement
     */
    public void setStatement(String statement) {
        this.statement = statement;
    }

    public String getScope() {
        return scope;
    }


    public void setScope(String scope) {
        this.scope = scope;
    }

}
