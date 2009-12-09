public class ExampleClient {
    
    /*@ normal_behaviour
      @   ensures \result == 0;
      @*/
    static int m() {
	ExampleSubject s = new ExampleSubject();
	ExampleObserver o = new ExampleObserver(s);
	s.addObserver(o);
	s.change();
	s.notifyObservers();	
	return s.value() - o.value();
    }
}
