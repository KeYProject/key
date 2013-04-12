package de.uka.ilkd.key.logic;

/**
 * Label attached to the implication when a loop body execution terminated
 * normally without any exceptions, returns or breaks
 * in branch "Body Preserves Invariant" of applied "Loop Invariant" rules
 * to show the loop invariant. 
 */
public class LoopInvariantNormalBehaviorTermLabel implements ITermLabel {
   /**
    * The unique name of this label.
    */
   public static final Name NAME = new Name("LoopInvariantNormalBehavior");

   /**
    * The only instance of this class.
    */
	public static LoopInvariantNormalBehaviorTermLabel INSTANCE = new LoopInvariantNormalBehaviorTermLabel();
	
	/**
	 * Constructor to forbid multiple instances.
	 */
	private LoopInvariantNormalBehaviorTermLabel() {		
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