package de.uka.ilkd.key.visualdebugger;

// TODO: Auto-generated Javadoc
/**
 * The Class LocalVariableDescriptor.
 */
public class LocalVariableDescriptor {

    /** The name. */
    private String name;
    
    /** The type. */
    private String type;
    
    /** The declaring method. */
    private String declaringMethod;
    
    /** The line. */
    private int line;
    
    /** The column. */
    private int column;
    
    /**
     * Instantiates a new local variable descriptor.
     * 
     * @param name the name
     * @param type the type
     * @param line the line
     * @param column the column
     */
    public LocalVariableDescriptor(String name, String type, int line,
            int column, String declaringMethod) {
        super();
        this.name = name;
        this.type = type;
        this.line = line;
        this.column = column;
        this.declaringMethod = declaringMethod;
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
     * Gets the type.
     * 
     * @return the type
     */
    public String getType() {
        return type;
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
     * Gets the column.
     * 
     * @return the column
     */
    public int getColumn() {
        return column;
    }

    public String getDeclaringMethod() {
        return declaringMethod;
    }
    
}
