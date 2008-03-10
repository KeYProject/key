package de.uka.ilkd.key.visualdebugger;

import java.util.List;

// TODO: Auto-generated Javadoc
/**
 * The Class WatchpointDescriptor.
 */
public class WatchpointDescriptor {

    /** The name. */
    private String name;

    /** The watch expression. */
    private String expression;

    /** The line. */
    private int line;

    /** The column. */
    private int column;

    /** The declaring method. */
    private String declaringType;

    /** The declaring method. */
    private String declaringMethod;

    /** The line. */
    private String varName;

    /** The column. */
    private String source;

    /** The is local. */
    private boolean isLocal = false;

    /** The local variables. */
    private List<LocalVariableDescriptor> localVariables;

    private List<String> parameterTypes;

    /**
     * Instantiates a new watchpoint descriptor.
     * 
     * @param name
     *                the name
     * @param line
     *                the line
     * @param column
     *                the column
     * @param declaringType
     *                the declaring type
     * @param varName
     *                the var name
     * @param source
     *                the source
     * @param isLocal
     *                the is local
     */

    public WatchpointDescriptor(String name, String expression, int line,
            int column, String declaringType, String varName, String source,
            boolean isLocal, List<LocalVariableDescriptor> localVariables,
            List<String> parameterTypes) {
        super();
        this.name = name;
        this.expression = expression;
        this.line = line;
        this.column = column;
        this.declaringType = declaringType;
        this.varName = varName;
        this.source = source;
        this.localVariables = localVariables;
        this.isLocal = isLocal;
        this.parameterTypes = parameterTypes;
    }

    public WatchpointDescriptor() {

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
     * Sets the name.
     * 
     * @param name
     *                the new name
     */
    public void setName(String name) {
        this.name = name;
    }

    /**
     * Gets the line.
     * 
     * @return the line
     */
    public int getLine() {
        return line;
    }

    /**
     * Sets the line.
     * 
     * @param line
     *                the new line
     */
    public void setLine(int line) {
        this.line = line;
    }

    /**
     * Gets the column.
     * 
     * @return the column
     */
    public int getColumn() {
        return column;
    }

    /**
     * Sets the column.
     * 
     * @param column
     *                the new column
     */
    public void setColumn(int column) {
        this.column = column;
    }

    /**
     * Gets the declaring type.
     * 
     * @return the declaring type
     */
    public String getDeclaringType() {
        return declaringType;
    }

    /**
     * Sets the declaring type.
     * 
     * @param declaringType
     *                the new declaring type
     */
    public void setDeclaringType(String declaringType) {
        this.declaringType = declaringType;
    }

    /**
     * Gets the var name.
     * 
     * @return the var name
     */
    public String getVarName() {
        return varName;
    }

    /**
     * Sets the var name.
     * 
     * @param varName
     *                the new var name
     */
    public void setVarName(String varName) {
        this.varName = varName;
    }

    /**
     * Gets the source.
     * 
     * @return the source
     */
    public String getSource() {
        return source;
    }

    /**
     * Sets the source.
     * 
     * @param source
     *                the new source
     */
    public void setSource(String source) {
        this.source = source;
    }

    /**
     * Checks if is local.
     * 
     * @return true, if is local
     */
    public boolean isLocal() {
        return isLocal;
    }

    /**
     * Sets the local.
     * 
     * @param isLocal
     *                the new local
     */
    public void setLocal(boolean isLocal) {
        this.isLocal = isLocal;
    }

    public List<String> getParameterTypes() {
        return parameterTypes;
    }

    public void setParameterTypes(List<String> parameterTypes) {
        this.parameterTypes = parameterTypes;
    }

    public String getExpression() {
        return expression;
    }

    public List<LocalVariableDescriptor> getLocalVariables() {
        return localVariables;
    }

    public void setLocalVariables(
            List<LocalVariableDescriptor> localVariables) {
        this.localVariables = localVariables;
    }

    public String getDeclaringMethod() {
        return declaringMethod;
    }

    public void setDeclaringMethod(String declaringMethod) {
        this.declaringMethod = declaringMethod;
    }

    public void setExpression(String expression) {
        this.expression = expression;
    }
}
