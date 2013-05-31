package de.uka.ilkd.key.logic;

/**
 * Label attached to the modality which executes a loop body 
 * in branch "Body Preserves Invariant" of applied "Loop Invariant" rules. 
 */
public class LoopBodyTermLabel implements ITermLabel {
   /**
    * The unique name of this label.
    */
   public static final Name NAME = new Name("LoopBody");

   /**
    * The only instance of this class.
    */
	public static LoopBodyTermLabel INSTANCE = new LoopBodyTermLabel();
	
	/**
	 * Constructor to forbid multiple instances.
	 */
	private LoopBodyTermLabel() {		
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
		return NAME.toString();
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

	/**
	 * {@inheritDoc}
	 */
   @Override
   public Name name() {
      return NAME;
   }
}