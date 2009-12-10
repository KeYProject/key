public class ExampleClient {
    
    //not yet verified (needs public invariants)
    /*@ normal_behaviour
      @   ensures \result == 0;
      @*/
    static int m() {
	ExampleSubject s = new ExampleSubject();
	ExampleObserver o = new ExampleObserver(s);
	s.addObserver(o);
	//s.change();
	s.notifyObservers();	
	return s.value() - o.value();
    }
}
