// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.visualdebugger.watchpoints;

import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;

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
    
    /** Set this to true, if you want to test if the expression might be true. */
    private boolean testPossible = false;
    
    /** The self. */
    private ProgramVariable self = null;
    
    /** The flavor. */
    private int flavor = 0;
    
    /** A list of all parameters from the corresponding program method. */
    private List<String> parameterTypes;
    
    /** The watchpoint parsed as KeY data structure. */
    private Term composedTerm;
    
    /** The watchpoint parsed as KeY data structure. */
    private Term rawTerm;
    
    /** The method where the local variables belong to. */
    private ProgramMethod programMethod = null;
    
    /** The positions where the local variables occurred in the method. */
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
     * Checks if this watchpoint is local.
     * 
     * @return true, if is watchpoint is local
     */
    public boolean isLocal() {
        if(getLocalVariables() == null) return false;
        else if(getLocalVariables().size() > 0 ) return true;
        return false;
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

    /**
     * Gets the parameter types.
     * 
     * @return the parameter types
     */
    public List<String> getParameterTypes() {
        return parameterTypes;
    }

    /**
     * Sets the parameter types.
     * 
     * @param parameterTypes the new parameter types
     */
    public void setParameterTypes(List<String> parameterTypes) {
        this.parameterTypes = parameterTypes;
    }
    
    /**
     * Gets the orginial local variables.
     * 
     * @return the orginial local variables
     */
    public List<LocationVariable> getOrginialLocalVariables() {
        return orginialLocalVariables;
    }

    /**
     * Sets the orginial local variables.
     * 
     * @param orginialLocalVariables the new orginial local variables
     */
    public void setOrginialLocalVariables(
            List<LocationVariable> orginialLocalVariables) {
        this.orginialLocalVariables = orginialLocalVariables;
    }

    /**
     * Gets the program method.
     * 
     * @return the program method
     */
    public ProgramMethod getProgramMethod() {
        return programMethod;
    }

    /**
     * Sets the program method.
     * The method in which the watchpoint was set (if local watchpoint).
     * 
     * @param programMethod the new program method
     */
    public void setProgramMethod(ProgramMethod programMethod) {
        this.programMethod = programMethod;
    }

    /**
     * Gets the key positions, i.e. a list of integers
     * identifying the positions of local variables used by this watchpoint
     * in a method, beginning with zero.
     * 
     * @return the key positions
     */
    public List<Integer> getKeyPositions() {
        return keyPositions;
    }

    /**
     * Sets the key positions.
     * 
     * @param keyPositions the new key positions
     */
    public void setKeyPositions(List<Integer> keyPositions) {
        this.keyPositions = keyPositions;
    }

    /**
     * Gets the flavor.
     * 
     * @return the flavor
     */
    public int getFlavor() {
        return flavor;
    }

    /**
     * Sets the flavor, i.e. the type of the quantification.
     * Default value is of the flavor is 0, which is existential
     * quantification.
     * Universal quantification is 1.
     * 
     * @param flavor the new flavor
     */
    public void setFlavor(int flavor) {
        this.flavor = flavor;
    }

    /**
     * Gets the self variable for this watchpoint.
     * 
     * @return the self
     */
    public ProgramVariable getSelf() {
        return self;
    }

    /**
     * Sets the self.
     * 
     * @param self the new self
     */
    public void setSelf(ProgramVariable self) {
        this.self = self;
    }

    /**
     * Test possible.
     *       
     * @return true, if the watchpoint should try to evaluate the sheer possibilty
     */
    public boolean testPossible() {
        return testPossible;
    }

    /**
     * Sets the test for possibility.
     * If this is set to true the visual debugger will try to find out
     * if it is at least possible that the specified condition holds. 
     * Therefore we try to show the validity of a watchpoint as usual. 
     * But if the proof cannot be closed the term watchpoint term will
     * be negated and another proof is started. If this cannot be
     * closed either, it is possible that the watchpoint is true.
     * 
     * @param testPossible the new test for possibility
     */
    public void setTestForPossibility(boolean testPossible) {
        this.testPossible = testPossible;
    }

    /**
     * Gets the composed term, 
     * i.e. the updates for the self variable and local variable names + watchpoint.
     * 
     * @return the composed term
     */
    public Term getComposedTerm() {
        return composedTerm;
    }

    /**
     * Sets the composed term,
     * i.e. watchpoint term including the updates for the self 
     * variable and local variable names + watchpoint.
     * 
     * @param composedTerm the new composed term
     */
    public void setComposedTerm(Term composedTerm) {
        this.composedTerm = composedTerm;
    }

    /**
     * Gets the raw term.
     * 
     * @return the raw term
     */
    public Term getRawTerm() {
        return rawTerm;
    }

    /**
     * Sets the raw term, after parsing.
     * 
     * @param rawTerm the new raw term
     */
    public void setRawTerm(Term rawTerm) {
        this.rawTerm = rawTerm;
    }
}
