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
   public static final Name NAME = new Name("SE");

   /**
    * The ID for the first modality with this label.
    */
   public static final int START_ID = 1;
   
   /**
    * The unique ID of this term label in the {@link Sequent}.
    */
   private int id;
	
	/**
	 * Constructor.
	 * @param id The unique ID of this term label in the {@link Sequent}.
	 */
	public SymbolicExecutionTermLabel(int id) {
	   this.id = id;
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
		return NAME.toString() + "(" + getId() + ")";
	}

   /**
    * {@inheritDoc}
    */
	@Override
   public Object getChild(int i) {
	   switch (i) {
	      case 0 : return getId();
  	      default : return null;
	   }
   }

   /**
    * {@inheritDoc}
    */
	@Override
   public int getChildCount() {
      return 1;
   }

	/**
	 * Returns the unique ID of this label in the {@link Sequent}.
	 * @return The unique ID of this label in the {@link Sequent}.
	 */
   public int getId() {
      return id;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Name name() {
      return NAME;
   }
}
