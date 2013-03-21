package de.uka.ilkd.key.logic;

/**
 * Label attached to a symbolic execution thread. 
 * Currently realized as singleton. In case one wants to track and distinguish 
 * different lines of execution, this needs to be changed.
 */
public class SymbolicExecutionTermLabel implements ITermLabel {
   /**
    * The unique name of this label.
    */
   public static final String NAME = "SE";

   /**
    * The only instance of this class.
    */
	public static SymbolicExecutionTermLabel INSTANCE = new SymbolicExecutionTermLabel();
	
	/**
	 * Constructor to forbid multiple instances.
	 */
	private SymbolicExecutionTermLabel() {		
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
		return NAME;
	}

   /**
    * {@inheritDoc}
    */
	@Override
   public ITermLabel getChild(int i) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
	@Override
   public int getChildCount() {
      return 0;
   }
}
