// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.watchpoints;

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
    
    /** The column. */ //TODO change to position
    private int position;
    
    /**
     * Instantiates a new local variable descriptor.
     * 
     * @param name the name
     * @param type the type
     * @param line the line
     * @param position the column
     */
    public LocalVariableDescriptor(String name, String type, int line,
            int position, String declaringMethod) {
        super();
        this.name = name;
        this.type = type;
        this.line = line;
        this.position = position;
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
    public int getPosition() {
        return position;
    }

    public String getDeclaringMethod() {
        return declaringMethod;
    }
    
}
