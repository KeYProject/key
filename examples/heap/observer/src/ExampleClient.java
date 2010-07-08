public class ExampleClient {
    
    //proof has about 250'000 nodes
    
    /*@ normal_behaviour
      @   ensures \result == 0;
      @*/
    static int m() {
	ExampleSubject s = new ExampleSubject();
	ExampleObserver o = new ExampleObserver(s);
	s.addObserver(o);
	s.notifyObservers();
	return s.value() - o.value();
    }
}
