public final class MultiCatch {
    /*@ ensures true; requires true; */
    public void m() throws Exception {
        // Simple multi-catch with two exception types
        try {
            doSomethingRisky();
        } catch (ArrayIndexOutOfBoundsException | AssertionError e) {
            System.out.println("Caught exception: " + e);
        }
        
        // Multi-catch with three exception types
        try {
            doAnotherRiskyThing();
        } catch (IllegalArgumentException | IndexOutOfBoundsException | InterruptedException e) {
            handleError(e);
        }
        
        // Mixed single and multi-catch
        try {
            doComplexOperation();
        } catch (NullPointerException e) {
            System.out.println("Null pointer!");
        } catch (IndexOutOfBoundsException | IllegalArgumentException e) {
            System.out.println("Illegal state or argument");
        } catch (Exception e) {
            System.out.println("Other exception");
        }
    }
    
    /*@ ensures true; requires true; */
    private void doSomethingRisky() throws ArrayIndexOutOfBoundsException, AssertionError {
        // might throw
    }
    
    /*@ ensures true; requires true; */
    private void doAnotherRiskyThing() throws IllegalArgumentException, IndexOutOfBoundsException, InterruptedException {
        // might throw
    }
    
    /*@ ensures true; requires true; */
    private void doComplexOperation() throws NullPointerException, IndexOutOfBoundsException, IllegalArgumentException, Exception {
        // might throw
    }
    
    /*@ ensures true; requires true; */
    private void handleError(Exception e) {
        // handle error
    }
}