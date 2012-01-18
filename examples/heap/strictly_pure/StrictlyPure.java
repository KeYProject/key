class StrictlyPure {

    int field;

    // We use the new keyword "\less_than_nothing" to specify
    // strict purity.

    /*@ requires true;
      @ assignable \less_than_nothing;
      @ ensures \result == field;
      @*/
    int strictlyPureMethod() {
	// assignable means modifies in KeY!
	// intermediate states may change the values of locations.
	
	field ++;
	field --;

	return field;
    }


    /*@ requires field == 42;
      @ ensures field == 42;
      @ ensures \dl_heap() == \old(\dl_heap());
      @*/
    void useStrictlyPureMethod() {
	return strictlyPureMethod();
    }

    /* WARNING: If you use the line
     *  ensures \dl_heap() == \old(\dl_heap());
     *
     * in a specification of a contract, you are likely
     * to encounter an infinite loop when using the contract.
     * Rather use the equivalent and more powerfull
     *  assignable \less_than_nothing;
     */
}
