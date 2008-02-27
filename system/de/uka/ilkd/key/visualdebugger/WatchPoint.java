package de.uka.ilkd.key.visualdebugger;

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
    /** The method in which the expression was set. For fields it will be set to "Field theField".  */
    private final String method;
    /** The line where the watchpoint was set. */
    private final String statement_line;
    
    private boolean enabled = true;
    private final boolean GLOBAL_WATCHPOINT;
    
    /** The type of the local variable the watchpoint was set on. */
    private final String typeOfLV;
    
    /** The name of the local variable the watchpoint was set on. */
    private final String nameOfLV;
    private int offset = 0;
    
    public String getInType() {
        return declaringType;
    }
    public String getTypeOfLV() {
        return typeOfLV;
    }
    public String getNameOfLV() {
        return nameOfLV;
    }
    public int getOffset() {
        return offset;
    }
    /**
     * Instantiates a new watch point.
     * 
     * Use this constructor to instaniate a new watch point for a global field or a constant.
     * 
     * @param expression the expression
     * @param typeOfSource the type of the source where the watchpoint was set
     * @param method the method
     * @param statement_line the statement_line
     */
    public WatchPoint(String name, String expression, String method,
            String statement_line, String typeOfSource) {
        super();
        this.name = name;
        this.expression = expression;
        this.method = method;
        this.statement_line = statement_line;
        this.declaringType = typeOfSource;
        this.typeOfLV = "n/a";
        this.nameOfLV = "n/a";
        GLOBAL_WATCHPOINT = true;
    }
    /**
     * Instantiates a new watch point.
     * 
     * Use this constructor to instaniate a new watch point for a local variable.
     * 
     * @param expression the expression
     * @param inType the type of the source where the watchpoint was set
     * @param method the method
     * @param statement_line the statement_line
     */
    public WatchPoint(String name, String expression, String method,
            String statement_line, String inType, String typeOfLV, String nameOfLV, int offset) {
        super();
        this.name = name;
        this.expression = expression;
        this.method = method;
        this.statement_line = statement_line;
        this.declaringType = inType;
        this.typeOfLV = typeOfLV;
        this.nameOfLV = nameOfLV;
        this.offset = offset;
        GLOBAL_WATCHPOINT = false;
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


    public String getName() {
        return name;
    }

    public boolean isEnabled() {
        return enabled;
    }

    public void setEnabled(boolean isEnabled) {
        this.enabled = isEnabled;
    }
    public boolean isGLOBAL_WATCHPOINT() {
        return GLOBAL_WATCHPOINT;
    }
}
