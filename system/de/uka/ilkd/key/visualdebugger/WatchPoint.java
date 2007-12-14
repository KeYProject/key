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
    private String statement_line;
    
    /**
     * Instantiates a new watch point.
     * 
     * @param expression the expression
     * @param file the file
     * @param method the method
     * @param statement_line the statement_line
     */
    public WatchPoint(String expression, String method,
            String statement_line, String file) {
        super();
        this.expression = expression;
        this.method = method;
        this.statement_line = statement_line;
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
     * Gets the file.
     * 
     * @return the file
     */
    public String getFile() {
        return file;
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



}
