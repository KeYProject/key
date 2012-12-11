package de.uka.ilkd.key.logic;

/**
 * Label attached to a symbolic execution thread. 
 * Currently realized as singleton. In case one wants to track and distinguish 
 * different lines of execution, this needs to be changed.
 */
public class SymbolicExecutionLabel implements ITermLabel {

	public static SymbolicExecutionLabel INSTANCE = new SymbolicExecutionLabel();
	
	private SymbolicExecutionLabel() {		
	}
	
	/**
	 * {@inheritDoc}
	 */
	public boolean equals(Object o) {
		return this == o;
	}
		
	/**
	 * {@inheritDoc}
	 */
	public String toString() {
		return "SE";
	}
	
	
}
